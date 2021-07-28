#!/bin/bash

ITERATIONS=10

echo "Running experiments.."

if [ "$3" == "rewritten" ];then
	echo "experiment;asymptotic;rewritten real time;rewritten user time;rewritten sys time;rewritten meval time" > $4
else
	echo "experiment;asymptotic;native real time;native user time;native sys time;native trigger time;native meval time" > $4
fi

for dir in $1/*/
do
    dir=${dir%*/}            # remove the trailing "/"
    experiment="${dir##*/}"  # print everything after the final "/"
	
	echo "Running experiment $experiment for $ITERATIONS iterations"
	for iteration in $( seq 1 $ITERATIONS ); do
		
		./measure-single-asymptotic.sh $1 $experiment baseline $3 >> $4
		
		for asymptotic in $2; do
			./measure-single-asymptotic.sh $1 $experiment $asymptotic $3 >> $4
		done
	done
done

echo "Done."