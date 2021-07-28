#!/bin/bash

ITERATIONS=10

echo "Running experiments.."

echo "experiment;asymptotic;rewritten real time;rewritten user time;rewritten sys time;rewritten meval time" > $3

for dir in $1/*/
do
    dir=${dir%*/}            # remove the trailing "/"
    experiment="${dir##*/}"  # print everything after the final "/"
	
	echo "Running experiment $experiment for $ITERATIONS iterations"
	for iteration in $( seq 1 $ITERATIONS ); do
		
		./measure-single-asymptotic.sh $1 $experiment baseline >> $3
		
		for asymptotic in $2; do
			./measure-single-asymptotic.sh $1 $experiment $asymptotic >> $3
		done
	done
done

echo "Done."