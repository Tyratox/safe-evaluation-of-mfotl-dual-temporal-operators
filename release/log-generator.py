import argparse
import random
import os
import numpy as np
import re

parser = argparse.ArgumentParser()
parser.add_argument('--output',
                    help='Output path', required=True)
parser.add_argument('--formula',
                    help='The formula file', required=True)
parser.add_argument('--pattern',
                    help="Sets the pattern of the log. Possible values: until, always, eventually", required=True)
parser.add_argument('--length',
                    help="Sets the length of the log. Default value: 10000")
parser.add_argument('--n',
                    help="Sets the number of assignments to x and y. Default value: 10")


args = parser.parse_args()

output = args.output
formula_path = args.formula
length = args.length or 10000
n = int(args.n) or 10
pattern = args.pattern


length = int(length)


def write_file(f, text):
    with open(f, "w") as text_file:
        text_file.write(text)


def read_file(filename):
    with open(filename) as f:
        content = f.read()

    return content


def read_lines(filename):
    with open(filename) as f:
        content = f.read().splitlines()

    return content


def insert_variables(formula, variables):
    for variable in variables:
        formula = formula.replace(variable, str(variables[variable]))
    return formula


formula = read_file(os.path.join(formula_path)).strip()
if "AND" in formula:
    formula = re.split("\sAND\s", formula)[1][1:-1]


interval = re.findall(r'\[\d+,(?:\*|\d+)\]', formula)[0][1:-1].split(",")
if (int(interval[0]) > length):
    print(
        f'The interval lower bound ({interval[0]}) is larger than the requested log length ({str(length)})!')
    exit()


subformulas = re.split(r'\sRELEASE\[\d+,(?:\*|\d+)\]\s', formula)
lhs = subformulas[0][1:-1]
rhs = subformulas[1][1:-1]

lhs_predicates = []
rhs_predicates = []

negated_lhs = "NOT" in lhs

if not(lhs in ["TRUE", "FALSE"]):
    lhs_predicates.append(lhs.replace(
        "(NOT A(x))", "A(x)").replace("(NOT A(x,y))", "A(x,y)"))

if not(rhs in ["TRUE", "FALSE"]):
    rhs_predicates.append(rhs)

predicates = lhs_predicates + rhs_predicates

log = []

print("Generating log of length " + str(length))

variables = ["x", "y"]


def generate_assignments():
    assignments = []

    for i in range(0, n):
        assignment = {
            "x": random.randint(0, 10 ** 9),
            "y": random.randint(0, 10 ** 9)
        }
        assignments.append(assignment)

    return assignments


def gen_log_entry(t, preds, assignments, additional_assignments=[], negative_predicates=[], negative_assignments=[]):
    return "@" + str(t) + " " + " ".join(list(set([insert_variables(p, a) for p in preds for a in assignments]).union(set([insert_variables(p, a) for p in predicates for a in additional_assignments])).difference(set([insert_variables(p, a) for p in negative_predicates for a in negative_assignments]))))


def append_to_log(log, t, preds, assignments, additional_assignments=[], negative_predicates=[], negative_assignments=[]):
    log.append(gen_log_entry(t, preds, assignments,
                             additional_assignments, negative_predicates, negative_assignments))


i = 0
t = 0

# repeat chunks in the size of the interval
while i < length:
    if interval[1] == "*":
        print("Unbounded release is not supported!")
        exit()
    else:
        upper_bound = min(i + int(interval[1]), length)

    lower_bound = min(i + int(interval[0]), length)

    if pattern == "always":

        # one assignment for all entries. at least rhs
        assignments = generate_assignments()

        # print("The historically assignments are")
        # print(assignments)

        while i < upper_bound:

            # additional assignments, just s.t. the log isn't perfectly uniform
            additional_assignments = generate_assignments()

            if random.uniform(0, 1) < 0.5:
                t = t+1

            append_to_log(log, t, rhs_predicates,
                          assignments, additional_assignments)

            i = i+1

    elif pattern == "until":
        # print("place rhs of since at " + str(loc))

        assignments = generate_assignments()
        assignment_per_loc = {}
        for assignment in assignments:
            # choose a log index where phi / the lhs occurs. must be within the interval!
            loc = random.randint(lower_bound, upper_bound)

            # the location might already be in the dictionary
            if loc in assignment_per_loc:
                # then append
                assignment_per_loc[loc].append(assignment)
            else:
                # otherwise just set it
                assignment_per_loc[loc] = [assignment]

        # [0, a-1] have to include all assignments + some random ones
        while i < lower_bound:
            additional_assignments = generate_assignments()

            if random.uniform(0, 1) < 0.5:
                t = t+1

            append_to_log(log, t, rhs_predicates,
                          assignments, additional_assignments)
            i = i+1

        # from there on only generate rhs with the at least same assignments until the end of the interval is reached
        while i < upper_bound - (int(interval[0])):
            a_lhs = []

            # collect all assignments that have to appear after i
            for loc in assignment_per_loc:
                if loc == i:
                    a_lhs = a_lhs + assignment_per_loc[loc]

            if random.uniform(0, 1) < 0.5:
                t = t+1

            additional_assignments = generate_assignments()

            if negated_lhs:
                # generate rhs and random, subtract lhs
                log.append("@" + str(t) + " " + " ".join(list(set([insert_variables(p, a) for p in rhs_predicates for a in assignments]).union(set([insert_variables(
                    p, a) for p in predicates for a in additional_assignments])).difference(set([insert_variables(p, a) for p in lhs_predicates for a in a_lhs])))))
            else:
                log.append("@" + str(t) + " " + " ".join(list(set([insert_variables(p, a) for p in lhs_predicates for a in a_lhs]).union(set([insert_variables(
                    p, a) for p in rhs_predicates for a in assignments])).union(set([insert_variables(p, a) for p in predicates for a in additional_assignments])))))

            i = i+1

            # remove all lhs from assignments after printing phi and psi together at loc, only holds up until this entry
            for a in a_lhs:
                assignments.remove(a)

        while i < upper_bound:
            # the rest can be filled with completely random entries
            assignments = generate_assignments()

            if random.uniform(0, 1) < 0.5:
                t = t+1

            append_to_log(log, t, predicates, assignments)
            i = i+1

    elif pattern == "eventually":

        if interval[0] == "0":
            print(
                "For pattern 'eventually', the lower bound of the intervall cannot be 0!")
            exit(0)

        # first a entries are (almost) random as well
        log_start = []
        while i < lower_bound:

            assignments = generate_assignments()

            if random.uniform(0, 1) < 0.5:
                t = t+1

            append_to_log(log_start, t, predicates, assignments)
            i = i+1

        # the first a entries contain one occurence of the lhs
        assignments = generate_assignments()
        assignment_per_idx = {}
        for assignment in assignments:
            # choose a log index where phi / the lhs occurs. must be within the interval!
            idx = random.randint(0, len(log_start) - 1)

            # the location might already be in the dictionary
            if idx in assignment_per_idx:
                # then append
                assignment_per_idx[idx].append(assignment)
            else:
                # otherwise just set it
                assignment_per_idx[idx] = [assignment]

        for idx in assignment_per_idx:
            t_eventually = re.findall(r'@\d+\s', log_start[idx])[0][1:-1]
            additional_assignments = generate_assignments()
            log_start[idx] = "@" + str(t_eventually) + " " + " ".join(
                list(set([insert_variables(p, a) for p in lhs_predicates for a in assignment_per_idx[idx]]).union(set([insert_variables(p, a) for p in predicates for a in additional_assignments]))))

        log = log + log_start

        # last entries are completely random
        while i < upper_bound:

            assignments = generate_assignments()

            if random.uniform(0, 1) < 0.5:
                t = t+1

            append_to_log(log, t, predicates, assignments)

            i = i+1

write_file(os.path.join(output), "\n".join(log) + "\n")
