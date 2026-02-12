# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *


def to_not_and_or(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    # Task 3.5
    rules = {
        '->': Formula.parse('(~p|q)'),
        '<->': Formula.parse('((p&q)|(~p&~q))'),
        '+': Formula.parse('((p&~q)|(~p&q))'),
        '-&': Formula.parse('~(p&q)'),
        '-|': Formula.parse('~(p|q)'),
        'T': Formula.parse('(p|~p)'),
        'F': Formula.parse('(p&~p)')
    }
    return formula.substitute_operators(rules)


def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # Task 3.6a
    f = to_not_and_or(formula)

    if is_variable(f.root) or is_constant(f.root):
        return f

    if is_unary(f.root):
        return Formula('~', to_not_and(f.first))

    left = to_not_and(f.first)
    right = to_not_and(f.second)

    if f.root == '|':
        return Formula('~', Formula('&', Formula('~', left), Formula('~', right)))

    return Formula('&', left, right)


def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # Task 3.6b
    f = to_not_and_or(formula)

    if is_variable(f.root):
        return f

    if is_unary(f.root):
        inside_formula = to_nand(f.first)
        return Formula('-&', inside_formula, inside_formula)

    left = to_nand(f.first)
    right = to_nand(f.second)

    if f.root == '&':
        not_and = Formula('-&', left, right)
        return Formula('-&', not_and, not_and)

    if f.root == '|':
        left_not = Formula('-&', left, left)
        right_not = Formula('-&', right, right)
        return Formula('-&', left_not, right_not)

    return f


def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    # Task 3.6c
    f = to_not_and_or(formula)

    if is_variable(f.root):
        return f

    if is_unary(f.root):
        inside_formula = to_implies_not(f.first)
        return Formula('~', inside_formula)

    left = to_implies_not(f.first)
    right = to_implies_not(f.second)

    if f.root == '&':
        return Formula('~', Formula('->', left, Formula('~', right)))

    if f.root == '|':
        return Formula('->', Formula('~', left), right)

    return f


def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # Task 3.6d
    f = to_not_and_or(formula)

    if is_variable(f.root):
        return f

    if is_constant(f.root):
        return Formula('->', Formula('F'), Formula('F'))

    if is_unary(f.root):
        inside_formula = to_implies_false(f.first)
        return Formula('->', inside_formula, Formula('F'))

    left = to_implies_false(f.first)
    right = to_implies_false(f.second)

    if f.root == '&':
        return Formula('->', Formula('->', left, Formula('->', right, Formula('F'))), Formula('F'))

    if f.root == '|':
        return Formula('->', Formula('->', left, Formula('F')), right)

    return f
