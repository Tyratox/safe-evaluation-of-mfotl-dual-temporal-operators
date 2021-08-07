#!/bin/bash
cd "$1/$2"

TIMEFORMAT='%3R;%3U;%3S'

if [ ! -f ./formula-$3.txt ]; then
	exit 0
fi

time_rewritten=$(time (../../../monpoly -formula ./formula-$3.txt -log ./log-$3.txt -sig ./signature.txt -no_rw -verified -no_trigger  > ./out-rewritten.txt) 2>&1)
rewritten_meval_time=$(cat ./out-rewritten.txt | grep meval | sed "s/meval: //" | awk '{n += $1}; END{print n}')

rm ./out-rewritten.txt

echo "$2;$3;$time_rewritten;$rewritten_meval_time"