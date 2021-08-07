#!/bin/bash

ITERATIONS=1

echo "Running experiments.."

echo "experiment;asymptotic;native real time;native user time;native sys time;native trigger time;native meval time;update;result;join;keys" > ./measurements-debug.csv

for dir in ./experiments-debug/*/
do
    dir=${dir%*/}            # remove the trailing "/"
    experiment="${dir##*/}"  # print everything after the final "/"
	
	echo "Running experiment $experiment for $ITERATIONS iterations"
	for iteration in $( seq 1 $ITERATIONS ); do
		./measure-single-debug.sh $experiment baseline >> ./measurements-debug.csv
		#./measure-single-debug.sh $experiment 2n >> ./measurements-debug.csv
		./measure-single-debug.sh $experiment 2l >> ./measurements-debug.csv
		#./measure-single-debug.sh $experiment 4n >> ./measurements-debug.csv
		./measure-single-debug.sh $experiment 4l >> ./measurements-debug.csv
		#./measure-single-debug.sh $experiment 8n >> ./measurements-debug.csv
		./measure-single-debug.sh $experiment 8l >> ./measurements-debug.csv
		#./measure-single-debug.sh $experiment 16n >> ./measurements-debug.csv
		./measure-single-debug.sh $experiment 16l >> ./measurements-debug.csv
	done
done

echo "Done."