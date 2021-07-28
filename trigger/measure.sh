#!/bin/bash

ITERATIONS=10

echo "Running experiments.."

echo "experiment;rewritten real time;rewritten user time;rewritten sys time;rewritten meval time;native real time;native user time;native sys time;native trigger time;native meval time" > ./measurements.csv

for dir in ./experiments/*/
do
    dir=${dir%*/}            # remove the trailing "/"
    experiment="${dir##*/}"  # print everything after the final "/"
	
	echo "Running experiment $experiment for $ITERATIONS iterations"
	for iteration in $( seq 1 $ITERATIONS ); do
		./measure-single.sh $experiment >> ./measurements.csv
	done
done

echo "Done."