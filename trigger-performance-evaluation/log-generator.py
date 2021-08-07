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
                    help="Sets the pattern of the log. Possible values: since, historically, once", required=True)
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


subformulas = re.split(r'\sTRIGGER\[\d+,(?:\*|\d+)\]\s', formula)
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
        upper_bound = length
    else:
        upper_bound = min(i + int(interval[1]), length)

    if pattern == "historically":

        # one assignment for all entries. at least rhs
        assignments = generate_assignments()

        # print("The historically assignments are")
        # print(assignments)

        while i < upper_bound - (int(interval[0])):

            # additional assignments, just s.t. the log isn't perfectly uniform
            additional_assignments = generate_assignments()

            if random.uniform(0, 1) < 0.5:
                t = t+1

            append_to_log(log, t, rhs_predicates,
                          assignments, additional_assignments)

            i = i+1

        # last a entries are random for interval I = [a, b]
        while i < upper_bound:

            assignments = generate_assignments()

            if random.uniform(0, 1) < 0.5:
                t = t+1

            append_to_log(log, t, predicates, assignments)

            i = i+1

    elif pattern == "since":
        # print("place rhs of since at " + str(loc))

        assignments = generate_assignments()
        assignment_per_loc = {}
        for assignment in assignments:
            # choose a log index where phi / the lhs occurs together with the rhs. must be within the interval!
            loc = random.randint(i, upper_bound - (int(interval[0])))

            # the location might already be in the dictionary
            if loc in assignment_per_loc:
                # then append
                assignment_per_loc[loc].append(assignment)
            else:
                # otherwise just set it
                assignment_per_loc[loc] = [assignment]

        a_rhs = []

        # from there on only generate rhs with the at least same assignments until the end of the interval is reached
        while i < upper_bound - (int(interval[0])):

            # this only once, r_rhs os collected over all
            a_lhs = []

            # collect all assignments that have to appear after i
            for loc in assignment_per_loc:
                if loc == i:
                    a_lhs = a_lhs + assignment_per_loc[loc]
                    a_rhs = a_rhs + assignment_per_loc[loc]

            # additional assignments, just s.t. the log isn't perfectly uniform
            additional_assignments = generate_assignments()

            if random.uniform(0, 1) < 0.5:
                t = t+1

            if negated_lhs:
                # generate rhs and random, subtract lhs
                log.append("@" + str(t) + " " + " ".join(list(set([insert_variables(p, a) for p in rhs_predicates for a in a_rhs]).union(set([insert_variables(
                    p, a) for p in predicates for a in additional_assignments])).difference(set([insert_variables(p, a) for p in lhs_predicates for a in a_lhs])))))
            else:
                log.append("@" + str(t) + " " + " ".join(list(set([insert_variables(p, a) for p in lhs_predicates for a in a_lhs]).union(set([insert_variables(
                    p, a) for p in rhs_predicates for a in a_rhs])).union(set([insert_variables(p, a) for p in predicates for a in additional_assignments])))))
            i = i+1

        # [0, a-1] can again be filled with random assignments
        while i < upper_bound:
            assignments = generate_assignments()

            if random.uniform(0, 1) < 0.5:
                t = t+1

            append_to_log(log, t, predicates, assignments)
            i = i+1

        pass
    elif pattern == "once":

        if interval[0] == "0":
            print("For pattern 'once', the lower bound of the intervall cannot be 0!")
            exit(0)

        # first few entries are completely random
        while i < upper_bound - (int(interval[0])):

            assignments = generate_assignments()

            if random.uniform(0, 1) < 0.5:
                t = t+1

            append_to_log(log, t, predicates, assignments)

            i = i+1

        # last a entries are (almost) random as well
        log_end = []
        while i < upper_bound:

            assignments = generate_assignments()

            if random.uniform(0, 1) < 0.5:
                t = t+1

            append_to_log(log_end, t, predicates, assignments)

            i = i+1
        # but the last a entries contain one occurence of the lhs
        assignments = generate_assignments()
        assignment_per_idx = {}
        for assignment in assignments:
            # choose a log index where phi / the lhs occurs. must be within the interval!
            idx = random.randint(0, len(log_end) - 1)

            # the location might already be in the dictionary
            if idx in assignment_per_idx:
                # then append
                assignment_per_idx[idx].append(assignment)
            else:
                # otherwise just set it
                assignment_per_idx[idx] = [assignment]

        for idx in assignment_per_idx:
            t_once = re.findall(r'@\d+\s', log_end[idx])[0][1:-1]
            additional_assignments = generate_assignments()
            log_end[idx] = "@" + str(t_once) + " " + " ".join(
                list(set([insert_variables(p, a) for p in lhs_predicates for a in assignment_per_idx[idx]]).union(set([insert_variables(p, a) for p in predicates for a in additional_assignments]))))

        log = log + log_end

write_file(os.path.join(output), "\n".join(log) + "\n")
