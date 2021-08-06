# Setup

1. Build `monpoly` from the code of [commit ea2a4d4](https://bitbucket.org/jshs/monpoly/commits/c84bf85bf3423fbe10130889fadaa47b39d6a414): [Download](https://bitbucket.org/jshs/monpoly/get/c84bf85bf3423fbe10130889fadaa47b39d6a414.tar.gz).
2. Download this git repo and override the files in `monpoly/trigger-performance-evaluation` and `monpoly/release-performance-evaluation` with the files located in `trigger/` and `release/` respectively.

# Verify Table and Plots

If you just want to verify the generation of table and the plots in the thesis, skip the first few steps in Experiments and just run `table-generator.py`, `asymptotic-plot-generator.py` and `asymptotic-plot-generator-rewritten.py` directly on the downloaded data (CSVs).

# Verify Experiments
## Comparison Experiments for Trigger

Relevant scripts: `table-generator.py`, `generate-experiments.py`, `log-generator.py`, `measure.sh`, `measure-single.sh`.

1. `cd trigger/`
2. In order to verify the results of the thesis, the same experiments should be downloaded but it is also possible to generate new ones.
	
	- Download the experiments `experiments-comparison.zip` used in the thesis from [here](https://github.com/Tyratox/safe-evaluation-of-mfotl-dual-temporal-operators/releases/tag/1.0) and extract them to the folder `./experiments`.
	
	- Run `python generate-experiments.py`. This will create the folder `./experiments` in the current working directory and fill it with the different experiments. Internally `generate-experiments.py` executes `log-generator.py` and hence one should set the current working directory to be the folder containing the two scripts. (Step 1)
	
3. Run `./measure.sh`. This will run all experiments in the folder `./experiments` 10 times by executing `./measure-single.sh` multiple times and write the results to `./measurements.csv`.
4. Run `python table-generator.py --measurements ./measurements.csv --output {DIR}` where `{DIR}` is the path to the output directory such as the current working directory `./`. The script will then write the file `table.tex` relative to the given output directory. If standard deviations should be shown in the table, add the flag `--stds`. The file `table.tex` can then be compiled to a pdf or opened in a text editor.

## Asymptotic Experiments for Trigger

Relevant scripts: `asymptotic-plot-generator.py`, `asymptotic-plot-generator-rewritten.py`, `generate-asymptotic-experiments.py`, `log-generator.py`, `measure-asymptotic.sh`, `measure-single-asymptotic.sh`.

1. `cd trigger/`
2. In order to verify the results of the thesis, the same experiments should be downloaded but it is also possible to generate new ones.
	
	- Download the experiments `experiments-asymptotic-trigger.zip` and `experiments-asymptotic-rewritten-trigger.zip` used in the thesis from [here](https://github.com/Tyratox/safe-evaluation-of-mfotl-dual-temporal-operators/releases/tag/1.0) and extract them to the folders `./experiments-asymptotic` and `./experiments-asymptotic-rewritten`.
	
	- Run `generate-asymptotic-experiments.py --output {DIR} --length {l} --n {n} --intervals {Is} --asymptotics {asym}`. This will create the folder `{DIR}` and fill it with the different experiments. The parameters `l` and `n` set the values for the baseline. `Is` and `asym` both allow multiple arguments. The different arguments must be enclosed in `"` and seperated by spaces. `Is` must be a subset of `"[0,*]", "[0, b]", "[a,*]", "[a,b]"` and `asym` a subset of `"2n", "2l", "2c", "4n", "4l", "4c", "8n", "8l", "8c"` where `c` corresponds to increasing both `l` and `n`. Internally `generate-asymptotic-experiments.py` executes `log-generator.py` and hence one should set the current working directory to be the folder containing the two scripts. (Step 1)
	
3. Run `./measure-asymptotic.sh ./experiments-asymptotic {asym} native ./measurements-asymptotic.csv`. This will run all experiments in the folder `./experiments-asymptotic` 10 times using the specialized algorithm by executing `./measure-single-asymptotic.sh` multiple times and write the results to `./measurements-asymptotic.csv`. The parameter `asym` once again contains the asymptotic values that should be measured but in contrast to step 3 the format required for bash is a little different: For the bash script all values must be passed as a single string enclosed in quotes, separated by spaces, e.g. `"2l 2n 8n 4l"`.

4. Run `asymptotic-plot-generator.py --measurements ./measurements-asymptotic.csv --output {DIR}`. This will generate a plot per experiment in the folder `DIR`.

5. Run `./measure-asymptotic.sh ./experiments-asymptotic-rewritten {asym} rewritten ./measurements-asymptotic-rewritten.csv`. This will run all experiments in the folder `./experiments-asymptotic-rewritten` 10 times using the translated formulas by executing `./measure-single-asymptotic.sh` multiple times and write the results to `./measurements-asymptotic-rewritten.csv`.

6. Run `asymptotic-plot-generator-rewritten.py --measurements ./measurements-asymptotic-rewritten.csv --output {DIR}`. This will generate a plot per experiment in the folder `DIR`.

## Asymptotic Experiments for Release

Relevant scripts: `asymptotic-plot-generator-rewritten.py`, `generate-asymptotic-experiments.py`, `log-generator.py`, `measure-asymptotic.sh`, `measure-single-asymptotic.sh`.

1. `cd release/`
2. In order to verify the results of the thesis, the same experiments should be downloaded but it is also possible to generate new ones.
	
	- Download the experiments `experiments-asymptotic-rewritten-release.zip` used in the thesis from [here](https://github.com/Tyratox/safe-evaluation-of-mfotl-dual-temporal-operators/releases/tag/1.0) and extract them to the folder `./experiments-asymptotic-rewritten`.
	
	- Run `generate-asymptotic-experiments.py --output {DIR} --length {l} --n {n} --intervals {Is} --asymptotics {asym}`. The parameters are the same as the ones described in step two of "Asymptotic Experiments for Trigger". Internally `generate-asymptotic-experiments.py` also executes `log-generator.py` and hence one should set the current working directory to be the folder containing the two scripts. (Step 1) Note that the files `generate-asymptotic-experiments.py` and `log-generator.py` are different for Trigger and Release.

3. Run `./measure-asymptotic.sh ./experiments-asymptotic-rewritten {asym} ./measurements-asymptotic-rewritten.csv`. This will run all experiments in the folder `./experiments-asymptotic-rewritten` 10 times using the translated formulas for Release by executing `./measure-single-asymptotic.sh` multiple times and write the results to `./measurements-asymptotic-rewritten.csv`.

4. Run `asymptotic-plot-generator-rewritten.py --measurements ./measurements-asymptotic-rewritten.csv --output {DIR}`. This will generate a plot per experiment in the folder `DIR`. Note that the script `asymptotic-plot-generator-rewritten.py` is the same for Trigger and Release.