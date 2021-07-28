#!/bin/bash
cd "./experiments/$1"

TIMEFORMAT='%3R;%3U;%3S'

ulimit -s 60000
time_rewritten=$(time (../../../monpoly -formula ./formula-baseline.txt -no_trigger -log ./log-baseline.txt -sig ./signature.txt -no_rw -verified > ./out-rewritten.txt) 2>&1)
# rewritten_loop_time=$(cat ./out-rewritten.txt | grep loop | sed "s/loop: //" | awk '{n += $1}; END{print n}')

ulimit -s 60000
rewritten_meval_time=$(cat ./out-rewritten.txt | grep meval | sed "s/meval: //" | awk '{n += $1}; END{print n}')

time_native=$(time (../../../monpoly -formula ./formula-baseline.txt -log ./log-baseline.txt -sig ./signature.txt -no_rw -verified  > ./out-native.txt) 2>&1)
trigger_time=$(cat ./out-native.txt | grep mmtaux | sed "s/mmtaux: //" | awk '{n += $1}; END{print n}')
# native_loop_time=$(cat ./out-native.txt | grep loop | sed "s/loop: //" | awk '{n += $1}; END{print n}')
native_meval_time=$(cat ./out-native.txt | grep meval | sed "s/meval: //" | awk '{n += $1}; END{print n}')

# check if the output of monpoly was correct. we might find some bugs this way
cat ./out-rewritten.txt | grep @ > ./out-rewritten-clean.txt
cat ./out-native.txt | grep @ > ./out-native-clean.txt

hash1=$(sha256sum ./out-rewritten-clean.txt | awk '{print $1}')
hash2=$(sha256sum ./out-native-clean.txt | awk '{print $1}')

if [ "$hash1" != "$hash2" ]; then
	printf "The outputs for experiment $1 do not match!\n" > ./check.txt
	printf "\$sha256sum ./out-rewritten-clean.txt: $hash1\n" >> ./check.txt
	printf "\$sha256sum ./out-native-clean.txt: $hash2\n" >> ./check.txt
fi

# even though we simply discard out-rewritten, it's more comparable this way
# rm ./out-rewritten.txt
# rm ./out-native.txt

echo "$1;$time_rewritten;$rewritten_meval_time;$time_native;$trigger_time;$native_meval_time"
