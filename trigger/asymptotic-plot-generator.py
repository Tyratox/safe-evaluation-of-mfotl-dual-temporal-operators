import argparse
import random
import os
import numpy as np
import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D

asymptotic_order = ["baseline", "2l", "4l", "8l",
                    "baseline-n", "2n", "4n", "8n",
                    "baseline-c", "2c", "4c", "8c"]


def index_to_key(idx):
    if "trigger" in idx[0]:
        # don't apply the function on the first level
        return idx

    return idx.map(asymptotic_order.index)


def err(correct, approximation):
    x = np.average((correct - approximation) ** 2)
    return x


parser = argparse.ArgumentParser()
parser.add_argument('--measurements',
                    help='The measurement csv', required=True)
parser.add_argument('--output',
                    help='The output directory', required=True)
# parser.add_argument( '--yscale', help='The scale of the y-axis. Default: linear')


args = parser.parse_args()

measurements = args.measurements
output = args.output
# yscale = args.yscale

df = pd.read_csv(measurements, sep=";", quotechar='"', skipinitialspace=True)

# df.drop(['rewritten real time', 'native real time',
#         'rewritten sys time', 'native sys time'], axis=1)

baseline_df2 = df[df['asymptotic'] == 'baseline'].copy()
baseline_df3 = baseline_df2.copy()
baseline_df2.loc[:, 'asymptotic'] = "baseline-n"
baseline_df3.loc[:, 'asymptotic'] = "baseline-c"

df = df.append(baseline_df2, ignore_index=True).append(
    baseline_df3, ignore_index=True)

experiments = pd.unique(df.sort_values(by=['experiment']).experiment)
asymptotics = pd.unique(df.sort_values(by=['asymptotic']).asymptotic)

df = df.groupby(['experiment', 'asymptotic']).agg({
    # 'native real time': ['mean', 'std'],
    'native meval time': ['mean', 'std'],
    'native trigger time': ['mean', 'std']
})

plt.rcParams.update({
    "text.usetex": True
})
plt.rcParams["figure.figsize"] = (8, 2)


def map_label(s):
    if s.endswith("l"):
        return r'$' + s.replace("l", r'l') + r'$'
    elif s.endswith("n"):
        return r'$' + s.replace("n", r'n') + r'$'
    elif s.endswith("c"):
        i = s[:-1]
        return r'$' + i + r'l, \:' + i + r'n' + r'$'
    else:
        return s


for experiment_name in experiments:
    exp = df.loc[[(experiment_name, a) for a in asymptotics]]
    exp = exp.sort_index(ascending=[True, True],
                         sort_remaining=False, key=index_to_key)

    labels = [a for e, a in exp.index]

    baseline1Index = labels.index("baseline")
    baseline2Index = labels.index("baseline-n")
    baseline3Index = labels.index("baseline-c")

    lExps = baseline2Index
    nExps = baseline3Index - baseline2Index
    cExps = len(labels) - baseline3Index

    x_l = np.array(list(range(lExps))) + 1
    x_n = np.array(list(range(nExps))) + 1
    x_c = np.array(list(range(cExps))) + 1

    # native_means = df['native real time']['mean'].to_numpy()
    native_meval_means = exp['native meval time']['mean'].to_numpy()
    native_mmtaux_means = exp['native trigger time']['mean'].to_numpy()

    # native_stds = df['native real time']['std'].to_numpy()
    native_meval_stds = exp['native meval time']['std'].to_numpy()
    native_mmtaux_stds = exp['native trigger time']['std'].to_numpy()

    A_l = np.vstack([np.log(x_l) * x_l, np.ones(len(x_l))]).T
    a_l, b_l = np.linalg.lstsq(
        A_l, native_mmtaux_means[0:baseline2Index], rcond=None)[0]

    A_n = np.vstack([np.log(x_n) * x_n, np.ones(len(x_n))]).T
    a_n, b_n = np.linalg.lstsq(
        A_n, native_mmtaux_means[baseline2Index:baseline3Index], rcond=None)[0]

    A_c = np.vstack([np.log(x_c) * x_c, np.ones(len(x_c))]).T
    a_c, b_c = np.linalg.lstsq(
        A_c, native_mmtaux_means[baseline3Index:], rcond=None)[0]

    linearFunctionX_l = np.linspace(1, baseline2Index, 100)
    # start at x = 0, a * x + b
    linearFunctionY_l = np.log(linearFunctionX_l) * \
        a_l * linearFunctionX_l + b_l
    lin_y_l = np.log(x_l) * a_l * x_l + b_l

    linearFunctionX_n = np.linspace(1, baseline3Index-baseline2Index, 100)
    # start at x = baseline2Index, a * x + b
    linearFunctionY_n = np.log(linearFunctionX_n) * \
        a_n * (linearFunctionX_n) + b_n
    lin_y_n = np.log(x_n) * a_n * x_n + b_n

    linearFunctionX_c = np.linspace(1, len(labels)-baseline3Index, 100)
    # start at x = baseline3Index, a * x + b
    linearFunctionY_c = np.log(linearFunctionX_c) * \
        a_c * (linearFunctionX_c) + b_c
    lin_y_c = np.log(x_c) * a_c * x_c + b_c

    B_c = np.vstack([np.log(x_c) * (x_c ** 2), np.log(x_c)
                     * x_c, np.ones(len(x_c))]).T
    m_c, p_c, q_c = np.linalg.lstsq(
        B_c, native_mmtaux_means[baseline3Index:], rcond=None)[0]

    quadraticFunctionX_c = np.linspace(1, len(labels)-baseline3Index, 100)
    quadraticFunctionY_c = m_c * np.log(quadraticFunctionX_c) * ((quadraticFunctionX_c) ** 2) + p_c * (np.log(quadraticFunctionX_c) * quadraticFunctionX_c) + \
        q_c  # start at x = 2, a * x^2 + b * x + c
    quad_y_c = m_c * np.log(x_c) * ((x_c) ** 2) + \
        p_c * (np.log(x_c) * x_c) + q_c

    # the width of the bars
    width = 0.35

    fig, (ax1, ax2, ax3) = plt.subplots(1, 3)
    # rects_native = ax.bar(x + width/2, native_means, width,
    #                       label='native', yerr=native_stds, ecolor='black', capsize=2, color='#e67e22')
    ax1.bar(x_l, native_meval_means[0:baseline2Index], width, label='meval', yerr=native_meval_stds[0:baseline2Index],
            ecolor='black', capsize=2, color='tab:orange')  # , color='#d35400'
    ax1.bar(x_l, native_mmtaux_means[0:baseline2Index], 0.75*width, label='mmtaux', yerr=native_mmtaux_stds[0:baseline2Index],
            ecolor='black', capsize=2, color='tab:green')  # , color='#2ecc71'

    ax1.set_ylim(bottom=0)
    ax1.plot(linearFunctionX_l, linearFunctionY_l, 'black', linestyle='dashed')

    custom_lines1 = [Line2D([0], [0], color="black", lw=1, linestyle='dashed')]
    legend1 = [
        f'linear, MSE: {err(native_meval_means[0:baseline2Index], lin_y_l):.2}']
    ax1.legend(custom_lines1, legend1)

    ax1.set_xticks(x_l)
    ax1.set_xticklabels(
        ["baseline" if ("baseline" in a) else map_label(a) for a in labels[0:baseline2Index]])

    ax2.bar(x_n, native_meval_means[baseline2Index:baseline3Index], width, label='meval', yerr=native_meval_stds[baseline2Index:baseline3Index],
            ecolor='black', capsize=2, color='tab:orange')  # , color='#d35400'
    ax2.bar(x_n, native_mmtaux_means[baseline2Index:baseline3Index], 0.75*width, label='mmtaux', yerr=native_mmtaux_stds[baseline2Index:baseline3Index],
            ecolor='black', capsize=2, color='tab:green')  # , color='#2ecc71'

    ax2.set_ylim(bottom=0)
    ax2.plot(linearFunctionX_n, linearFunctionY_n, 'black', linestyle='dashed')

    custom_lines2 = [Line2D([0], [0], color="black", lw=1, linestyle='dashed')]
    legend2 = [
        f'linear, MSE: {err(native_meval_means[baseline2Index:baseline3Index], lin_y_n):.2}']

    ax2.legend(custom_lines2, legend2)
    ax2.set_xticks(x_n)
    ax2.set_xticklabels(
        ["baseline" if ("baseline" in a) else map_label(a) for a in labels[baseline2Index:baseline3Index]])

    ax3.bar(x_c, native_meval_means[baseline3Index:], width, label='meval', yerr=native_meval_stds[baseline3Index:],
            ecolor='black', capsize=2, color='tab:orange')  # , color='#d35400'
    ax3.bar(x_c, native_mmtaux_means[baseline3Index:], 0.75*width, label='mmtaux', yerr=native_mmtaux_stds[baseline3Index:],
            ecolor='black', capsize=2, color='tab:green')  # , color='#2ecc71'

    ax3.set_ylim(bottom=0)
    ax3.plot(linearFunctionX_c, linearFunctionY_c, 'black', linestyle='dashed')
    ax3.plot(quadraticFunctionX_c, quadraticFunctionY_c,
             'black', linestyle='dotted')
    custom_lines3 = [Line2D([0], [0], color="black", lw=1, linestyle='dashed'),
                     Line2D([0], [0], color="black", lw=1, linestyle='dotted')
                     ]
    legend3 = [
        f'linear, MSE: {err(native_meval_means[baseline3Index:], lin_y_c):.2}',
        f'quadratic, MSE: {err(native_meval_means[baseline3Index:], quad_y_c):.2}',
    ]
    ax3.legend(custom_lines3, legend3, loc='upper left')
    ax3.set_xticks(x_c)
    ax3.set_xticklabels(
        ["baseline" if ("baseline" in a) else map_label(a) for a in labels[baseline3Index:]])

    fig.tight_layout()

    plt.savefig(os.path.join(output, f'{experiment_name}.png'), dpi=300)
    plt.close(fig)
