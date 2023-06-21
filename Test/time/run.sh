#!/usr/bin/bash
# usage:
#   seq ... | ./run.sh template.v

mdir="$(dirname "$0")"
root="$mdir/../.."
file="$1"
time="$(which time)"
name=$(basename "$file" | sed -e 's/\.v$//')
tmp="$mdir/_tmp/$name"

mkdir -p "$tmp"
first=1

while read -r n
do
	echo "N=$n"
	sed -e 's/2(\*PLACEHOLDER\*)/'${n}'/' "$file" > "$tmp/src.v"
	$time -f "COQC %es" -- coqc -R "$root" SLFun "$tmp/src.v" 2>&1 | tee "$tmp/out_${n}.txt"
	sed -f "$mdir"/extract.sed "$tmp/out_${n}.txt" > "$tmp/out_${n}.csv"

	if [ "$first" -eq 1 ]
	then
		gawk -e 'BEGIN{FS=":"; printf("N")}{printf(" %s",$1)}END{printf("\n")}' "$tmp/out_${n}.csv" > "$tmp/all.data"
		first=0
	fi
	gawk -e 'BEGIN{FS=":"; printf("'$n'")}{printf(" %s",$2)}END{printf("\n")}' "$tmp/out_${n}.csv" >> "$tmp/all.data"
	echo
done
