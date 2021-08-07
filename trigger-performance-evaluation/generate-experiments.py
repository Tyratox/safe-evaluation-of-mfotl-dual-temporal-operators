import os


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


# trigger
for interval in ["[a,*]"]:
    for lhs in ["FALSE", "A(x)", "(NOT A(x))", "A(x,y)", "(NOT A(x,y))"]:
        for log_type in ["historically", "since", "once"]:
            # once is only allowed for a > 0
            if log_type == "once" and (interval != "[a,*]" and interval != "[a,b]"):
                continue

            # if 0 is not in the interval, the lhs has to be A(x, y) (same set of free variables and not negated)
            if (interval == "[a,*]" or interval == "[a,b]") and (lhs != "A(x,y)"):
                continue

            if interval == "[a,b]":
                orig_length = 2 * 10 ** 2
            elif interval == "[a,*]":
                orig_length = 5 * 10 ** 2
            else:
                orig_length = 2 * 10 ** 3

            length = orig_length
            n = 10 ** 2
            interval_size = 0.4

            experiment = f'trigger-{int_to_s(interval)}-{lhs_to_s(lhs)}-{log_type}'
            print(f'Generating experiment {experiment}..')

            output = os.path.join(
                "./experiments", experiment)
            if not(os.path.isdir(output)):
                os.makedirs(output)

            formula_path = os.path.join(
                output, f'formula-baseline.txt')
            signature_path = os.path.join(output, "signature.txt")
            log_path = os.path.join(output, f'log-baseline.txt')

            write_file(
                formula_path, f'(C(x,y)) AND (({lhs}) TRIGGER{gen_int(interval, orig_length, interval_size)} ({rhs}))')

            if lhs == "A(x)" or lhs == "(NOT A(x))":
                write_file(signature_path, f'A(int)\nB(int,int)\nC(int,int)')
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
