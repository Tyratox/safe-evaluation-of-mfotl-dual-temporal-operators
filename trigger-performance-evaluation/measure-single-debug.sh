#!/bin/bash
cd "./experiments-debug/$1"

TIMEFORMAT='%3R;%3U;%3S'

time_native=$(time (../../../monpoly -formula ./formula-$2.txt -log ./log-$2.txt -sig ./signature.txt -no_rw -verified  > ./out-native.txt) 2>&1)

keys=$(cat ./out-native.txt | grep keys | sed "s/keys: //" | awk '{n += $1}; END{print n}')
join=$(cat ./out-native.txt | grep join | sed "s/join: //" | awk '{n += $1}; END{print n}')
#l1=$(cat ./out-native.txt | grep l1 | sed "s/l1: //" | awk '{n = $1 > n ? $1 : n}; END{print n}')
#l2=$(cat ./out-native.txt | grep l2 | sed "s/l2: //" | awk '{n = $1 > n ? $1 : n}; END{print n}')

#td1=$(cat ./out-native.txt | grep td1 | sed "s/td1: //" | awk '{n += $1}; END{print n}')
#td2=$(cat ./out-native.txt | grep td2 | sed "s/td2: //" | awk '{n += $1}; END{print n}')
#td3=$(cat ./out-native.txt | grep td3 | sed "s/td3: //" | awk '{n += $1}; END{print n}')
#td4=$(cat ./out-native.txt | grep td4 | sed "s/td4: //" | awk '{n += $1}; END{print n}')
#td5=$(cat ./out-native.txt | grep td5 | sed "s/td5: //" | awk '{n += $1}; END{print n}')
#td6=$(cat ./out-native.txt | grep td6 | sed "s/td6: //" | awk '{n += $1}; END{print n}')
#td7=$(cat ./out-native.txt | grep td7 | sed "s/td7: //" | awk '{n += $1}; END{print n}')

update=$(cat ./out-native.txt | grep update | sed "s/update: //" | awk '{n += $1}; END{print n}')
result=$(cat ./out-native.txt | grep result | sed "s/result: //" | awk '{n += $1}; END{print n}')

trigger_time=$(cat ./out-native.txt | grep mmtaux | sed "s/mmtaux: //" | awk '{n += $1}; END{print n}')
native_meval_time=$(cat ./out-native.txt | grep meval | sed "s/meval: //" | awk '{n += $1}; END{print n}')

rm ./out-native.txt

echo "$1;$2;$time_native;$trigger_time;$native_meval_time;$update;$result;$join;$keys"
