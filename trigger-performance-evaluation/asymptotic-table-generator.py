import argparse
import random
import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

asymptotic_order = ["l", "2l", "4l", "8l",
                    "n", "2n", "4n", "8n",
                    "c", "2c", "4c", "8c"]


def index_to_key(idx):
    if "trigger" in idx[0]:
        # don't apply the function on the first level
        return idx

    return idx.map(asymptotic_order.index)


def err(correct, approximation):
    x = np.average((correct - approximation) ** 2)
    return x

def write_file(f, text):
    with open(f, "w") as text_file:
        text_file.write(text)

def exp_to_formula(e):
    if "0-bounded" in e:
        interval = r'[0, b)'
    elif "0-unbounded" in e:
        interval = r'[0, \infty)'
    elif "a-bounded" in e:
        interval = r'[a, b)'
    elif "a-unbounded" in e:
        interval = r'[a, \infty)'

    if "lhs-0" in e:
        lhs = r'False'
    elif "lhs-1-neg" in e:
        lhs = r'\neg A(x)'
    elif "lhs-1" in e:
        lhs = r'A(x)'
    elif "lhs-2-neg" in e:
        lhs = r'\neg A(x, y)'
    elif "lhs-2" in e:
        lhs = r'A(x, y)'

    if "historically" in e:
        pattern = r'p_{1}'
    elif "since" in e:
        pattern = r'p_{2}'
    elif "once" in e:
        pattern = r'p_{3}'

    return r'$' + lhs + r'\: T_{' + interval + r'} \: B(x,y)$'

def exp_to_pattern(e):
    if "historically" in e:
        return "Historically"
    elif "since" in e:
        return "Since"
    elif "once" in e:
        return "Once"
    else:
        exit(-1)

def exp_to_params(e):
    #these are the parameters used for generating the experiments
    return '100', '100'

parser = argparse.ArgumentParser()
parser.add_argument('--measurements',
                    help='The measurement csv', required=True)
parser.add_argument('--output',
                    help='The output directory', required=True)
parser.add_argument('--stds', dest='stds', action='store_true')
parser.add_argument('--pdf', dest='pdf', action='store_true')
parser.set_defaults(stds=False)
parser.set_defaults(pdf=False)

args = parser.parse_args()

measurements = args.measurements
output = args.output
use_stds = args.stds
generate_pdf = args.pdf

df = pd.read_csv(measurements, sep=";", quotechar='"', skipinitialspace=True)

# df.drop(['rewritten real time', 'native real time',
#         'rewritten sys time', 'native sys time'], axis=1)
df['asymptotic'] = df['asymptotic'].apply(lambda x: 'l' if x == 'baseline' else x)

baseline_df2 = df[df['asymptotic'] == 'l'].copy()
baseline_df3 = baseline_df2.copy()
baseline_df2.loc[:, 'asymptotic'] = "n"
baseline_df3.loc[:, 'asymptotic'] = "c"

df = df.append(baseline_df2, ignore_index=True).append(
    baseline_df3, ignore_index=True)

experiments = pd.unique(df.sort_values(by=['experiment']).experiment)
asymptotics = pd.unique(df.sort_values(by=['asymptotic']).asymptotic)

df = df.groupby(['experiment', 'asymptotic']).agg({
    # 'native real time': ['mean', 'std'],
    'native meval time': ['mean', 'std'],
    'native trigger time': ['mean', 'std']
})


df.columns = [col[1] + " " + col[0]
              if col[1] != '' else col[0] for col in df.columns.values]

for experiment_name in experiments:
    exp = df.loc[[(experiment_name, a) for a in asymptotics]]
    exp = exp.sort_index(ascending=[True, True],
                         sort_remaining=False, key=index_to_key)

    
    exp = exp.reset_index()
    
    dfs = [exp.iloc[:4].copy().reset_index(drop=True), exp.iloc[4:8].copy().reset_index(drop=True), exp.iloc[8:].copy().reset_index(drop=True)]
    t = pd.DataFrame()

    for asym, exp in zip(['l', 'n', 'c'], dfs):
        x = exp.iloc[1:][['mean native meval time', 'mean native trigger time']].reset_index(drop=True).div(exp.iloc[:-1][['mean native meval time', 'mean native trigger time']].reset_index(drop=True))
        x.index = range(1,len(x)+1)

        exp[['factor native meval time', 'factor native trigger time']] = x[['mean native meval time', 'mean native trigger time']]
        
        #exp = exp.fillna(1.0)
        #exp = exp.round(2).astype(str)

        exp[r'$parameters$'] = exp['asymptotic'].apply(lambda x: 'n, l' if x == 'c' else '2n, 2l' if x == '2c' else '4n, 4l' if x == '4c' else '8n, 8l' if x == "8c" else x)
        exp[r'$time \texttt{meval}$'] = exp['mean native meval time']
        exp[r'$std$'] = exp['std native meval time']
        exp[r'$ratio$'] = exp['factor native meval time']
        exp[r'$time \texttt{mtaux}$'] = exp['mean native trigger time']
        exp[r'$std \texttt{mtaux}$'] = exp['std native trigger time']
        exp[r'$ratio\vphantom{ }$'] = exp['factor native trigger time']

        if use_stds:
            t = t.append(exp[[r'$parameters$', r'$time \texttt{meval}$', r'$std$', r'$ratio$', r'$time \texttt{mtaux}$', r'$std \texttt{mtaux}$', r'$ratio\vphantom{ }$']])
        else:
            t = t.append(exp[[r'$parameters$', r'$time \texttt{meval}$', r'$ratio$', r'$time \texttt{mtaux}$', r'$ratio\vphantom{ }$']])
    
    if use_stds:
        latex = t.to_latex(index=False, column_format="L R R R R R R", escape=False, float_format="%.2f", na_rep="")
    else:
        latex = t.to_latex(index=False, column_format="L R R R R", escape=False, float_format="%.2f", na_rep="")

    latex_list = latex.splitlines()
    latex_list.insert(len(latex_list)-6, '\midrule')
    latex_list.insert(len(latex_list)-11, '\midrule')

    l, n = exp_to_params(experiment_name)
    
    if generate_pdf:
        if not(os.path.isdir(output)):
            os.makedirs(output)

        write_file(os.path.join(output, f'table.tex'), '\n'.join(latex_list))

        path = os.path.join(output, f'table.tex')
        pdf = os.path.join(output, f'table.pdf')
        crop = os.path.join(output, f'table-crop.pdf')
        result = os.path.join(output, experiment_name + '.pdf')

        caption = f'Formula: & {exp_to_formula(experiment_name)}' + r'\\' + '\n' + f'Pattern: & {exp_to_pattern(experiment_name)}'

        with open(path, 'r') as original: data = original.read()
        with open(path, 'w') as modified:
            modified.write(r'\documentclass{article}\usepackage{booktabs}\usepackage{array}\newcolumntype{L}{>{$}l<{$}}\newcolumntype{R}{>{$}r<{$}}\pagestyle{empty}\begin{document}' + '\n' + \
                r'\begin{table}\centering' + '\n' + data + r'\\[1ex]' + '\n' + \
                    r'$l$ = ' + l + r', $n$ = ' + n + r'\\[0.5ex]' + \
                    r'\begin{tabular}{l @{$\:$} l}' + '\n' + caption + '\n' + r'\end{tabular}' + '\n' \
                r'\end{table}' + '\n' + r'\end{document}')
        os.system(f'pdflatex -output-directory {output} {path}')
        os.unlink(path)
        os.unlink(os.path.join(output, f'table.log'))
        os.unlink(os.path.join(output, f'table.aux'))
        os.system(f'pdfcrop {pdf}')
        os.unlink(pdf)
        os.system(f'mv {crop} {result}')
    else:
        if not(os.path.isdir(os.path.join(output, experiment_name))):
            os.makedirs(os.path.join(output, experiment_name))

        write_file(os.path.join(output, experiment_name, f'table.tex'), '\n'.join(latex_list))
        write_file(os.path.join(output, experiment_name, f'formula.tex'), exp_to_formula(experiment_name))
        write_file(os.path.join(output, experiment_name, f'pattern.tex'), exp_to_pattern(experiment_name))

        write_file(os.path.join(output, experiment_name, f'n.tex'), n)
        write_file(os.path.join(output, experiment_name, f'l.tex'), l)