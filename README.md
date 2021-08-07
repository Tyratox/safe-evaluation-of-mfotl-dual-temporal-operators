# Tables

To look at all tables, simply navigate to the folder `./tables`.

# Setup for verification

1. Build `monpoly` from the code of [commit  16d4a16](https://bitbucket.org/jshs/monpoly/commits/16d4a1663e5eaf25f3fed0b43cc29188ac28c070): [Download](https://bitbucket.org/jshs/monpoly/get/16d4a1663e5eaf25f3fed0b43cc29188ac28c070.tar.gz).

A copy of the directories `trigger-performance-evaluation` and `release-performance-evaluation` can also be found in this repo.

# Verify Tables

If you just want to verify the generation of tables in the thesis, skip the first few steps in Experiments and just run `table-generator.py`, `asymptotic-table-generator.py` and `asymptotic-table-generator-rewritten.py` directly on the downloaded data (CSVs).

# Verify Experiments
## Comparison Experiments for Trigger

Relevant scripts: `table-generator.py`, `generate-experiments.py`, `log-generator.py`, `measure.sh`, `measure-single.sh`.

1. `cd trigger-performance-evaluation/`
2. In order to verify the results of the thesis, the same experiments should be downloaded but it is also possible to generate new ones.
	
	- Download the experiments `experiments-comparison.zip` used in the thesis from [here](https://github.com/Tyratox/safe-evaluation-of-mfotl-dual-temporal-operators/releases/tag/1.0) and extract them to the folder `./experiments`.
	
	- Run `python generate-experiments.py`. This will create the folder `./experiments` in the current working directory and fill it with the different experiments. Internally `generate-experiments.py` executes `log-generator.py` and hence one should set the current working directory to be the folder containing the two scripts. (Step 1)
	
3. Run `./measure.sh`. This will run all experiments in the folder `./experiments` 10 times by executing `./measure-single.sh` multiple times and write the results to `./measurements.csv`.
4. Run `python table-generator.py --measurements ./measurements.csv --output {DIR}` where `{DIR}` is the path to the output directory such as the current working directory `./`. The script will then write the file `table.tex` relative to the given output directory. If standard deviations should be shown in the table, add the flag `--stds`. The file `table.tex` can then be compiled to a pdf or opened in a text editor.

## Asymptotic Experiments for Trigger

Relevant scripts: `asymptotic-table-generator.py`, `asymptotic-table-generator-rewritten.py`, `generate-asymptotic-experiments.py`, `log-generator.py`, `measure-asymptotic.sh`, `measure-single-asymptotic.sh`.

1. `cd trigger-performance-evaluation/`
2. In order to verify the results of the thesis, the same experiments should be downloaded but it is also possible to generate new ones.
	
	- Download the experiments `experiments-asymptotic-trigger.zip` and `experiments-asymptotic-rewritten-trigger.zip` used in the thesis from [here](https://github.com/Tyratox/safe-evaluation-of-mfotl-dual-temporal-operators/releases/tag/1.0) and extract them to the folders `./experiments-asymptotic` and `./experiments-asymptotic-rewritten`.
	
	- Run `generate-asymptotic-experiments.py --output {DIR} --length {l} --n {n} --intervals {Is} --asymptotics {asym}`. This will create the folder `{DIR}` and fill it with the different experiments. The parameters `l` and `n` set the values for the baseline. `Is` and `asym` both allow multiple arguments. The different arguments must be enclosed in `"` and seperated by spaces. `Is` must be a subset of `"[0,*]", "[0, b]", "[a,*]", "[a,b]"` and `asym` a subset of `"2n", "2l", "2c", "4n", "4l", "4c", "8n", "8l", "8c"` where `c` corresponds to increasing both `l` and `n`. Internally `generate-asymptotic-experiments.py` executes `log-generator.py` and hence one should set the current working directory to be the folder containing the two scripts. (Step 1)
	
3. Run `./measure-asymptotic.sh ./experiments-asymptotic {asym} native ./measurements-asymptotic.csv`. This will run all experiments in the folder `./experiments-asymptotic` 10 times using the specialized algorithm by executing `./measure-single-asymptotic.sh` multiple times and write the results to `./measurements-asymptotic.csv`. The parameter `asym` once again contains the asymptotic values that should be measured but in contrast to step 3 the format required for bash is a little different: For the bash script all values must be passed as a single string enclosed in quotes, separated by spaces, e.g. `"2l 2n 8n 4l"`.

4. Run `asymptotic-table-generator.py --measurements ./measurements-asymptotic.csv --output {DIR}`. This will generate a table per experiment in the folder `DIR` in a `.tex` file. For a pdf, add the flag `--pdf` and for standard deviations add `--stds`.

5. Run `./measure-asymptotic.sh ./experiments-asymptotic-rewritten {asym} rewritten ./measurements-asymptotic-rewritten.csv`. This will run all experiments in the folder `./experiments-asymptotic-rewritten` 10 times using the translated formulas by executing `./measure-single-asymptotic.sh` multiple times and write the results to `./measurements-asymptotic-rewritten.csv`.

6. Run `asymptotic-table-generator-rewritten.py --measurements ./measurements-asymptotic-rewritten.csv --output {DIR}`. This will generate a table per experiment in the folder `DIR` in a `.tex` file. For a pdf, add the flag `--pdf` and for standard deviations add `--stds`.

## Asymptotic Experiments for Release

Relevant scripts: `asymptotic-table-generator-rewritten.py`, `generate-asymptotic-experiments.py`, `log-generator.py`, `measure-asymptotic.sh`, `measure-single-asymptotic.sh`.

1. `cd release-performance-evaluation/`
2. In order to verify the results of the thesis, the same experiments should be downloaded but it is also possible to generate new ones.
	
	- Download the experiments `experiments-asymptotic-rewritten-release.zip` used in the thesis from [here](https://github.com/Tyratox/safe-evaluation-of-mfotl-dual-temporal-operators/releases/tag/1.0) and extract them to the folder `./experiments-asymptotic-rewritten`.
	
	- Run `generate-asymptotic-experiments.py --output {DIR} --length {l} --n {n} --intervals {Is} --asymptotics {asym}`. The parameters are the same as the ones described in step two of "Asymptotic Experiments for Trigger". Internally `generate-asymptotic-experiments.py` also executes `log-generator.py` and hence one should set the current working directory to be the folder containing the two scripts. (Step 1) Note that the files `generate-asymptotic-experiments.py` and `log-generator.py` are different for Trigger and Release.

3. Run `./measure-asymptotic.sh ./experiments-asymptotic-rewritten {asym} ./measurements-asymptotic-rewritten.csv`. This will run all experiments in the folder `./experiments-asymptotic-rewritten` 10 times using the translated formulas for Release by executing `./measure-single-asymptotic.sh` multiple times and write the results to `./measurements-asymptotic-rewritten.csv`.

4. Run `../trigger-performance-evaluation/asymptotic-table-generator-rewritten.py --measurements ./measurements-asymptotic-rewritten.csv --output {DIR}`. This will generate a table per experiment in the folder `DIR` in a `.tex` file. For a pdf, add the flag `--pdf` and for standard deviations add `--stds`. Note that the script `asymptotic-table-generator-rewritten.py` is the same for Trigger and Release.