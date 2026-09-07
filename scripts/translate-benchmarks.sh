#!/bin/bash

function usage() {
    cat <<-EOF
	Translates Alethe proofs to Lambdapi and checks them with lambdapi.

	Consumes the .alethe proofs produced by generate-benchmarks.sh and writes one
	Lambdapi module per proof into alethe-lp/proofs/.

	That directory is not arbitrary. Lambdapi resolves \`require open alethe.core\`
	by walking up from the file being checked to the nearest lambdapi.pkg, and the
	alethe package is not installed into the Lambdapi lib_root, so a generated
	proof only resolves from inside alethe-lp/. It is a *subdirectory* because
	alethe-lp/Makefile globs \`*.lp\` non-recursively, so proofs placed here are
	swept into neither \`make\` nor \`make install\`.

	Each proof is tried strictly first, then retried with --admit-unsupported, so
	the report distinguishes a proof that is fully translated from one leaning on
	an admitted rule.

	By default this looks for carcara in target/release and falls back to
	\`cargo run\`; override with \$CARCARA. Override lambdapi with \$LAMBDAPI.

	USAGE:
	    translate-benchmarks.sh [OPTIONS]

	OPTIONS:
	    -h, --help      Show this message.
	    -d <dir>        Directory to search for .alethe proofs.
	                    (default: benchmarks/small/simple-tests)
	    -o <dir>        Where to write the .lp modules.
	                    (default: alethe-lp/proofs)
	    -k, --keep      Do not clear the output directory first.

	EXIT STATUS:
	    Fails only if a proof translated but then did not check, which is the
	    signal worth acting on. A proof the backend cannot translate at all is
	    reported as "blocked" and does not fail the run: that is a known gap
	    (an unimplemented rule, or a sort the backend has no encoding for),
	    not a regression.
	EOF
}

set -u

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
src="$repo/benchmarks/small/simple-tests"
out="$repo/alethe-lp/proofs"
keep=""

while [ $# -gt 0 ]; do
    case "$1" in
        -h | --help) usage; exit 0 ;;
        -k | --keep) keep="true" ;;
        -d | -o)
            if [ "$#" -lt 2 ]; then
                echo "missing argument value"
                exit 1
            fi
            case "$1" in
                -d) src="$2" ;;
                -o) out="$2" ;;
            esac
            shift
            ;;
        *)
            echo "invalid argument: '$1'"
            echo
            usage
            exit 1
            ;;
    esac
    shift
done

if [ -z "${CARCARA:-}" ]; then
    if [ -x "$repo/target/release/carcara" ]; then
        CARCARA="$repo/target/release/carcara"
    else
        # No --release: this is a correctness check, not a benchmark, and building
        # release here would surprise anyone running it for the first time.
        CARCARA="cargo run -q --manifest-path $repo/Cargo.toml --bin carcara --"
    fi
fi
LAMBDAPI="${LAMBDAPI:-lambdapi}"

if ! command -v ${LAMBDAPI% *} &> /dev/null; then
    echo "lambdapi not found"
    echo "make sure that it is in your \$PATH, or that the \$LAMBDAPI variable is set"
    exit 1
fi

if [ ! -d "$src" ]; then
    echo "no such directory: $src"
    echo "run scripts/generate-benchmarks.sh first to produce the .alethe proofs"
    exit 1
fi

proofs=$(find "$src" -name '*.alethe' | sort)
if [ -z "$proofs" ]; then
    echo "no .alethe proofs under $src"
    exit 1
fi

mkdir -p "$out"
[ -n "$keep" ] || rm -f "$out"/*.lp
# Stale .lpo files make an unrelated module fail with an assertion in the loader,
# which looks like a real regression. Always start clean.
find "$repo/alethe-lp" -name '*.lpo' -delete

logs=$(mktemp -d)
report="$logs/report.tsv"
: > "$report"

# The parser flags cvc5 proofs need; harmless for proofs that do not.
parse_flags=(--expand-let-bindings --allow-int-real-subtyping)

while IFS= read -r f; do
    name=$(basename "$f" | sed 's/\.smt2.*//')
    # Lambdapi derives the module name from the file name, so it has to be a plain
    # identifier -- the same rule tests/test_example_files.rs applies.
    mod=$(basename "$f" .alethe | sed 's/[^A-Za-z0-9]/_/g')
    lp="$out/$mod.lp"

    if err=$($CARCARA translate lambdapi "$f" "${parse_flags[@]}" 2>&1 >"$lp"); then
        mode=strict
    elif err=$($CARCARA translate lambdapi "$f" "${parse_flags[@]}" --admit-unsupported 2>&1 >"$lp"); then
        mode=admitted
    else
        reason=$(printf '%s' "$err" | grep -oE 'rule `[a-z_0-9]+` is not supported|unreachable code: [A-Za-z]+' | head -1)
        printf '%s\t%s\t-\t%s\n' "$name" blocked "${reason:-see $logs}" >> "$report"
        printf '%s\n' "$err" > "$logs/translate-$mod.log"
        rm -f "$lp"
        continue
    fi

    # One lambdapi process per module: checking several at once trips the .lpo
    # loader on modules carrying string literals (see alethe-lp/README.md).
    # Deliberately no -w, which would hide critical-pair and axiom warnings.
    if cerr=$(cd "$out" && $LAMBDAPI check -v 0 "$mod.lp" 2>&1); then
        printf '%s\t%s\tcheck-ok\t\n' "$name" "$mode" >> "$report"
    else
        first=$(printf '%s' "$cerr" | sed 's/\x1b\[[0-9;]*m//g' \
            | grep -aoE "\[$mod\.lp:[0-9:.-]+\].*|Unknown symbol [^ ]*" | head -1)
        printf '%s\t%s\tcheck-FAIL\t%s\n' "$name" "$mode" "${first:-see $logs}" >> "$report"
        printf '%s\n' "$cerr" > "$logs/check-$mod.log"
    fi
done <<< "$proofs"

printf '%-38s %-9s %-11s %s\n' NAME TRANSLATE CHECK DETAIL
awk -F'\t' '{ printf "%-38s %-9s %-11s %s\n", $1, $2, $3, $4 }' "$report"
awk -F'\t' '
    { translate[$2]++; if ($3 != "-") check[$3]++ }
    END {
        printf "\ntranslate: strict %d, admitted %d, blocked %d\n",
            translate["strict"], translate["admitted"], translate["blocked"]
        printf "check:     ok %d, failed %d\n", check["check-ok"], check["check-FAIL"]
    }' "$report"
echo
echo "logs: $logs"

grep -q 'check-FAIL' "$report" && exit 1
exit 0
