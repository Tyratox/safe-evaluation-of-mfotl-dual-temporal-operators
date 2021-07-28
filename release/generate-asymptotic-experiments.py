import argparse
import os

parser = argparse.ArgumentParser()
parser.add_argument('--output',
                    help='The output directory', required=True)
parser.add_argument('--length',
                    help='The 1x log length (Default: 100)')
parser.add_argument('--n',
                    help='The 1x number of tuples (Default: 100)')
parser.add_argument('--intervals', nargs='+',
                    help='The intervals used, separated by spaces. (Default: ["[0,b]", "[a,b]"]:')
parser.add_argument('--asymptotics', nargs='+',
                    help='The asymptotic values used, separated by spaces. (Default: ["2n", "2l", "2c", "4n", "4l", "4c", "8n", "8l", "8c"])')
#parser.add_argument( '--yscale', help='The scale of the y-axis. Default: linear')


args = parser.parse_args()

output_dir = args.output
base_length = args.length or 10 ** 2
base_n = args.n or 10 ** 2
intervals = args.intervals or ["[0,b]", "[a,b]"]
asymptotics = args.asymptotics or [
    "2n", "2l", "2c", "4n", "4l", "4c", "8n", "8l", "8c"]

base_length = int(base_length)
base_n = int(base_n)


def gen_int(interval, length, interval_size):
    if interval == "[a,b]":
        interval = interval.replace(
            'a', str(int((1 - interval_size)/2 * length)))
        interval = interval.replace(
            'b', str(int((1 - (1 - interval_size)/2) * length)))
    elif interval == "[a,*]":
        interval = interval.replace(
            'a', str(int((1-interval_size) * length)))
    elif interval == "[0,b]":
        interval = interval.replace(
            'b', str(int(interval_size * length)))

    return interval


def write_file(f, text):
    with open(f, "w") as text_file:
        text_file.write(text)


rhs = "B(x,y)"


def lhs_to_s(lhs):
    if lhs == "FALSE":
        return "lhs-0"
    elif lhs == "A(x)":
        return "lhs-1"
    elif lhs == "(NOT A(x))":
        return "lhs-1-neg"
    elif lhs == "A(x,y)":
        return "lhs-2"
    elif lhs == "(NOT A(x,y))":
        return "lhs-2-neg"
    else:
        raise ValueError(f'Unknown lhs: {lhs}')


def int_to_s(interval):
    if interval == "[0,*]":
        return "0-unbounded"
    elif interval == "[0,b]":
        return "0-bounded"
    elif interval == "[a,*]":
        return "a-unbounded"
    elif interval == "[a,b]":
        return "a-bounded"
    else:
        raise ValueError(f'Unknown interval: {interval}')


# release
for interval in intervals:
    for lhs in ["FALSE", "A(x)", "(NOT A(x))", "A(x,y)", "(NOT A(x,y))"]:
        for log_type in ["always", "until", "eventually"]:
            for asymptotic in ["baseline"] + asymptotics:
                # once is only allowed for a > 0
                if log_type == "eventually" and (interval != "[a,*]" and interval != "[a,b]"):
                    continue

                # if 0 is not in the interval, the lhs has to be A(x, y) (same set of free variables and not negated)
                if (interval == "[a,*]" or interval == "[a,b]") and (lhs != "A(x,y)"):
                    continue

                if interval == "[0,*]" and asymptotic == "2i":
                    continue

                #orig_length = 10 ** 2

                length = base_length
                n = base_n
                interval_size = 0.75

                if asymptotic == "baseline":
                    pass
                elif asymptotic.endswith("n"):
                    n = int(asymptotic[:-1]) * n
                elif asymptotic.endswith("l"):
                    length = int(asymptotic[:-1]) * length
                elif asymptotic.endswith("c"):
                    n = int(asymptotic[:-1]) * n
                    length = int(asymptotic[:-1]) * length
                else:
                    print(f'Invalid asymptotic value: "{asymptotic}"!')
                    exit()

                experiment = f'release-{int_to_s(interval)}-{lhs_to_s(lhs)}-{log_type}'
                print(f'Generating experiment {experiment} ({asymptotic})..')

                output = os.path.join(output_dir, experiment)
                if not(os.path.isdir(output)):
                    os.makedirs(output)

                formula_path = os.path.join(
                    output, f'formula-{asymptotic}.txt')
                signature_path = os.path.join(output, "signature.txt")
                log_path = os.path.join(output, f'log-{asymptotic}.txt')

                write_file(formula_path,
                           f'(C(x,y)) AND (({lhs}) RELEASE{gen_int(interval, length, interval_size)} ({rhs}))')

                if lhs == "A(x)" or lhs == "(NOT A(x))":
                    write_file(signature_path,
                               f'A(int)\nB(int,int)\nC(int,int)')
                elif lhs == "A(x,y)" or lhs == "(NOT A(x,y))":
                    write_file(signature_path,
                               f'A(int,int)\nB(int,int)\nC(int,int)')
                else:
                    write_file(signature_path, f'B(int,int)\nC(int,int)')

                # to generate the log, execute the other script
                os.system(
                    f'python ./log-generator.py --formula {formula_path} --pattern {log_type} --output {log_path} --length {length} --n {n}')
                # print(
                #    f'Check execution time of experiment {experiment} ({asymptotic})..')
                #os.system(f'./measure-single.sh {experiment} {asymptotic}')
