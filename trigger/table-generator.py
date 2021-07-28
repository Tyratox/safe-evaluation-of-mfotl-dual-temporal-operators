import argparse
import random
import os
import numpy as np
import pandas as pd

parser = argparse.ArgumentParser()
parser.add_argument('--measurements',
                    help='The measurement csv', required=True)
parser.add_argument('--output',
                    help='The output path', required=True)
#parser.add_argument( '--yscale', help='The scale of the y-axis. Default: linear')


args = parser.parse_args()

measurements = args.measurements
output = args.output
#yscale = args.yscale

df = pd.read_csv(measurements, sep=";", quotechar='"', skipinitialspace=True)

# df.drop(['rewritten real time', 'native real time',
#         'rewritten sys time', 'native sys time'], axis=1)


def exp_sort_key(x):
    return x.map(lambda x: x.replace("0-unbounded", "1").replace("0-bounded", "2").replace("a-unbounded", "3").replace("a-bounded", "4").replace("-historically", "1").replace("-since", "2").replace("-once", "3"))


def split_experiment(x):
    splits = x.split("-")
    return pd.Series(["-".join(splits[:-1]), splits[-1]])


df = df.sort_values(by=['experiment'], key=exp_sort_key)
df[['experiment', 'pattern']] = df.experiment.apply(split_experiment)

experiments = pd.unique(df.experiment)

#print(df.sort_values(by=['experiment'], key=exp_sort_key))

df = df.groupby(['experiment', 'pattern'], sort=False).agg({
    # 'rewritten real time': ['mean', 'std'],
    'rewritten meval time': ['mean', 'std'],
    # 'native real time': ['mean', 'std'],
    'native meval time': ['mean', 'std'],
    'native trigger time': ['mean', 'std']
})


def map_exp(idx):
    e = idx[0]

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

    return r'$' + lhs + r'\: T_{' + interval + r'} \: B(x, y) $'


def idx_to_pattern(idx):
    return idx[1]


df['pattern'] = df.index.map(idx_to_pattern)
df['formula'] = df.index.map(map_exp)
df = df.reset_index(drop=True)

df.columns = [col[1] + " " + col[0]
              if col[1] != '' else col[0] for col in df.columns.values]
df = df.round(2).astype(str)

df['translated formula'] = r'$' + df['mean rewritten meval time'] + r'$'
#r' \pm ' + df['std rewritten meval time'] + r'$'

df['specialized algorithm'] = r'$' + df['mean native meval time'] + r'$'
# r' \pm ' + \ df['std native meval time'] + r'$'

df[r'\texttt{mtaux}'] = r'$' + df['mean native trigger time'] + r'$'
#+ r' \pm ' + df['std native trigger time'] + r'$'

df[['formula', 'pattern', 'translated formula', 'specialized algorithm', r'\texttt{mtaux}']
   ].to_latex(os.path.join(output, "table.tex"), index=False, column_format="l l p {2cm} p {2cm} l", escape=False)
