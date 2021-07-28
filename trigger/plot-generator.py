import argparse
import random
import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt

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


df = df.sort_values(by=['experiment'], key=exp_sort_key)
experiments = pd.unique(df.experiment)

#print(df.sort_values(by=['experiment'], key=exp_sort_key))

df = df.groupby(['experiment'], sort=False).agg({
    'rewritten real time': ['mean', 'std'],
    'rewritten meval time': ['mean', 'std'],
    'native real time': ['mean', 'std'],
    'native meval time': ['mean', 'std'],
    'native trigger time': ['mean', 'std']
})

plt.rcParams.update({
    "text.usetex": True
})

labels = []
last = ""
for e in experiments:
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

    current = e.replace("-historically", "").replace("-since",
                                                     "").replace("-once", "")
    if last == current:
        labels.append(r'$' + pattern + r'$')
    else:
        labels.append(
            r'$' + lhs + r'\: ${T}$_{' + interval + r'} \: B(x,y), \:' + pattern + r'$')

    last = current

#rewritten_means = df['rewritten real time']['mean'].to_numpy()
rewritten_meval_means = df['rewritten meval time']['mean'].to_numpy()
#native_means = df['native real time']['mean'].to_numpy()
native_meval_means = df['native meval time']['mean'].to_numpy()
native_mmtaux_means = df['native trigger time']['mean'].to_numpy()

#rewritten_stds = df['rewritten real time']['std'].to_numpy()
rewritten_meval_stds = df['rewritten meval time']['std'].to_numpy()
#native_stds = df['native real time']['std'].to_numpy()
native_meval_stds = df['native meval time']['std'].to_numpy()
native_mmtaux_stds = df['native trigger time']['std'].to_numpy()

#plt.rcParams["figure.figsize"] = (len(labels)+3, 5)

# the label locations
x = np.arange(len(labels))

# the width of the bars
width = 0.35

fig, ax = plt.subplots()
# rects_rewritten = ax.bar(x - width/2, rewritten_means, width,
#                          label='rewritten', yerr=rewritten_stds, ecolor='black', capsize=2, color='#3498db')
rects_rewritten_meval = ax.bar(x - width/2, rewritten_meval_means, width,
                               label='rewritten meval', yerr=rewritten_meval_stds, ecolor='black', capsize=2, color='tab:blue')  # , color='#2980b9'

# rects_native = ax.bar(x + width/2, native_means, width,
#                       label='native', yerr=native_stds, ecolor='black', capsize=2, color='#e67e22')
rects_native_meval = ax.bar(x + width/2, native_meval_means, width,
                            label='native meval', yerr=native_meval_stds, ecolor='black', capsize=2, color='tab:orange')  # , color='#d35400'
rects_native_mmtaux = ax.bar(x + width/2, native_mmtaux_means, 0.5*width,
                             label='mmtaux', yerr=native_mmtaux_stds, ecolor='black', capsize=2, color='tab:green')  # , color='#2ecc71'

# Add some text for labels, title and custom x-axis tick labels, etc.
#ax.set_ylabel('Running time of meval in seconds')
plt.xticks(rotation=30, ha='right')
ax.set_xticks(x)
ax.set_xticklabels(labels, fontsize=8)
# ax.legend()

plt.yscale('log')
# if "a-bounded" in experiment_name:
#     plt.yscale('log')
# else:
#     plt.yscale('linear')

# ax.bar_label(rects1, padding=3)
# ax.bar_label(rects2, padding=3)

fig.tight_layout()

plt.savefig(os.path.join(output, f'plot.png'), dpi=300)
