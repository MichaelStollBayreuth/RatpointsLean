"""The command lines of the suites errors, fuzz and regions of scripts/difftest.py.

CASES holds hand-written command lines for the checks that main.c makes on the coefficients, the
height and the options, for the options of the search, of the search region and of the output and
for the refusals of a form that is not squarefree, each with a note; STOP_CASES holds searches at a
large height that both programs stop at once; random_command_lines gives random ones, with words
that the readers of numbers of main.c accept or refuse in many ways, the options of the search
region among them, and options of the output with formats and strings, and random_output_options
random options of the output for a search; and random_region_line gives a search with a random
search region. An argument is a str or, for a byte string that is not UTF-8, bytes. A height that a
search could not finish (such as 2^63 - 1) is always followed by an option that fails, so that
neither program searches, or comes with a narrow search region (random_region_line), but in
STOP_CASES, which the errors suite runs with a short timeout and a cap on the memory.
"""
import math
from decimal import Decimal
from fractions import Fraction

C102 = ' '.join(['1'] + ['0'] * 100 + ['1'])          # 102 coefficients
C101 = ' '.join(['1'] + ['0'] * 99 + ['1'])           # 101 coefficients: degree 100

CASES = [
    # the number of arguments
    ([], 'no arguments: error 2 (banner and usage)'),
    (['1 0 1'], 'one argument: error 2'),
    # the coefficients
    (['abc', '10'], 'letters: error 11'),
    (['1 2 x', '10'], 'a letter after two numbers: error 11'),
    (['1 +2', '10', '-q'], 'a leading + is accepted'),
    ([' +3\t4\r', '10', '-q'], 'white space around and between, + accepted'),
    (['', '10'], 'empty list: error 5'),
    (['   ', '10'], 'only white space: error 5'),
    (['-', '10'], 'a lone -: error 11'),
    (['+', '10'], 'a lone +: error 11'),
    (['5', '10'], 'one coefficient: error 5'),
    (['1 2-', '10'], 'a sign after the digits: error 11'),
    (['1 --2', '10'], 'two signs: error 11'),
    (['1 2 3 - 4', '10'], 'a sign standing alone: error 11'),
    (['1,0,1', '10'], 'commas: error 11'),
    (['1.5 2', '10'], 'a decimal point: error 11'),
    (['1_000 2', '10'], 'a digit separator: error 11'),
    (['1\x0b0\x0c1\r', '10', '-q'], 'vertical tab and form feed are white space'),
    (['+1 +0 +1', '10', '-q'], 'all with +'),
    (['-0 1', '10', '-q'], '-0 is 0'),
    (['0001 0002', '10', '-q'], 'leading zeros'),
    (['1 0 0 0 100000000000000000000000000000000000000000001', '3', '-q'], 'a large coefficient'),
    ([C102, '10'], '102 coefficients: error 3'),
    ([C102, 'abc'], '102 coefficients and a bad height: error 3 comes first'),
    ([C102 + ' x', '10'], '102 coefficients, then a letter: error 11 comes first'),
    ([C101, '3', '-q'], '101 coefficients: accepted'),
    (['x', 'abc'], 'bad coefficients and bad height: error 11 comes first'),
    (['', 'abc'], 'empty list and bad height: error 5 comes first'),
    ([b'\xff 1', '10'], 'a byte that is not UTF-8: error 11'),
    (['1 \u00a02'.encode(), '10'], 'a no-break space (U+00A0, two bytes in UTF-8): error 11'),
    (['-q', '1 0 1', '10'], 'an option before the coefficients is read as the list: error 11'),
    (['1 0 1', '-q', '10'], 'an option in place of the height: error 4'),
    # the height
    (['1 0 1', '0'], 'height 0: error 4'),
    (['1 0 1', '-1'], 'height -1: error 4'),
    (['1 0 1', '-0'], 'height -0: error 4'),
    (['1 0 1', '+5', '-q'], 'height +5'),
    (['1 0 1', ' 7 ', '-q'], 'height with blanks around'),
    (['1 0 1', '10\r', '-q'], 'height with a carriage return'),
    (['1 0 1', '010', '-q'], 'height 010 is 10'),
    (['1 0 1', '9223372036854775807', '-g'], '2^63 - 1 is accepted (then -g: error 6)'),
    (['1 0 1', '+9223372036854775807', '-g'], '+(2^63 - 1) is accepted (then -g: error 6)'),
    (['1 0 1', '9223372036854775808', '-g'], '2^63: error 4'),
    (['1 0 1', '-9223372036854775808'], '-2^63: error 4'),
    (['1 0 1', '-9223372036854775809'], 'below -2^63: error 4'),
    (['1 0 1', '100000000000000000000000'], '10^23: error 4'),
    (['1 0 1', '1e3'], '1e3: error 4'),
    (['1 0 1', 'abc'], 'abc: error 4'),
    (['1 0 1', ''], 'empty height: error 4'),
    (['1 0 1', '+ 5'], 'a blank after the sign: error 4'),
    (['1 0 1', '0x10'], 'hexadecimal: error 4'),
    (['1 0 1', '10 0'], 'two numbers: error 4'),
    (['1 0 1', '1_0'], 'a digit separator: error 4'),
    (['1 0 1', '\u0661'.encode()], 'an Arabic-Indic digit one: error 4'),
    # the tuning options with arguments
    *[(['1 0 1', '5', '-q', '-' + o], '-%s without its argument: error 6' % o)
      for o in 'pFtnNRAPrUCQW'],
    *[(['1 0 1', '5', '-q', '-' + o, 'x'], '-%s x: error 6' % o) for o in 'pFtnNRAPrUCQW'],
    *[(['1 0 1', '5', '-q', '-' + o, ' 3 '], '-%s with blanks around: accepted' % o)
      for o in 'pFtnNRAPrUCQW'],
    (['1 0 1', '5', '-q', '-p', '9223372036854775807'], '-p 2^63 - 1'),
    (['1 0 1', '5', '-q', '-p', '9223372036854775808'], '-p 2^63: error 6'),
    (['1 0 1', '5', '-q', '-p', '-9223372036854775808'], '-p -2^63'),
    (['1 0 1', '5', '-q', '-p', '-9223372036854775809'], '-p below -2^63: error 6'),
    (['1 0 1', '5', '-q', '-p', '+3'], '-p +3'),
    (['1 0 1', '5', '-q', '-p', '5 5'], '-p with two numbers: error 6'),
    (['1 0 1', '5', '-q', '-p', ''], '-p with an empty argument: error 6'),
    (['1 0 1', '5', '-q', '-p', '5x'], '-p 5x: error 6'),
    (['1 0 1', '5', '-q', '-t', '0'], '-t 0'),
    (['1 0 1', '5', '-q', '-t', '-3'], '-t -3'),
    (['1 0 1', '5', '-q', '-t', '1\r'], '-t with a carriage return'),
    (['1 0 1', '5', '-q', '-n', '0', '-N', '0', '-P', '0'], 'zero moduli'),
    (['1 0 1', '5', '-q', '-A', '7', '-F', '-1'], 'odd values of -A and -F'),
    *[(['1 0 1', '5', '-q', '-r', v], '-r %r: accepted' % v)
      for v in ['inf', '-Infinity', 'INF', '1e400', '-1e400', '4.9e-324', '1e-400', '0x1p-3',
                '0x.8', '0X1P3', '1E+5', '+.5e-3', '0x1.8p1', '1.', '.5', '00.5', '0x1e5', '-0',
                ' 0.5 ', '1.7976931348623157e308', '0x1p-1075', '0X.8p+0']],
    *[(['1 0 1', '5', '-q', '-r', v], '-r %r: error 6' % v)
      for v in ['nan', 'NaN', '-nan', 'nan(1)', 'infinit', 'infx', '0x', '0x1p', '1e', '.', '',
                '1 2', '1,5', '306x', '1e+', '0xg', '1.5.3', '0x.p1', '- 1', '+-1', '1e5x',
                '0x1.p', 'i', 'in', 'infinityy', '1d', '1f', '0b1', '1_0']],
    (['1 0 1', '5', '-q', '-U', '1e-300'], '-U 1e-300'),
    (['1 0 1', '5', '-q', '-C', '0', '-Q', '-1', '-W', '-inf'], '-C 0 -Q -1 -W -inf'),
    # the options without an argument
    (['1 0 1', '5', '-q', '-j'], '-j'),
    (['1 0 1', '5', '-q', '-J'], '-J'),
    (['1 0 1', '5', '-q', '-j', '5'], '-j 5: the 5 is a word without -, error 6'),
    (['1 0 1', '5', '-q', '-v'], '-q -v'),
    (['1 0 1', '5', '-v', '-q'], '-v -q'),
    (['1 0 1', '5', '-quiet'], '-quiet is -q'),
    (['1 0 1', '5', '-qq'], '-qq is -q'),
    (['1 0 1', '5', '-qz'], '-qz is -q'),
    (['1 0 1', '5', '-q', '-jx'], '-jx is -j'),
    (['1 0 1', '5', '-q', '-pfoo', '5'], '-pfoo 5 is -p 5'),
    (['1 0 1', '5', '-q', '-rfoo', '0.5'], '-rfoo 0.5 is -r 0.5'),
    (['1 0 1', '5'], 'no -q: the report'),
    (['1 0 1', '5', '-v'], '-v: the report of -v (that of the library left out)'),
    (['1 0 1', '5', '-v', '-q'], '-v -q: -q cancels -v'),
    (['1 0 1', '5', '-q', '-v'], '-q -v: -q cancels -v'),
    (['1 0 1', '5', '-verbose', '-z'], '-verbose is -v'),
    # the options of the search: -k and -K (the reversal), -s and -S (the Sturm step)
    (['-1 0 9', '5', '-q', '-k'], '-k: no reversal, the points in the order of the reference'),
    (['-1 0 9', '5', '-q', '-K'], '-K: the reversal allowed, as by default'),
    (['-1 0 9', '5', '-q', '-k', '-K'], '-k -K: the last one wins, the reversal'),
    (['-1 0 9', '5', '-q', '-K', '-k'], '-K -k: the last one wins, no reversal'),
    (['-1 0 9', '5', '-q', '-kfoo'], '-kfoo is -k'),
    (['0 1 0 0 4', '5', '-q', '-k'], '-k on a polynomial that ratpoints reverses in case 1'),
    (['0 1 0 2', '5', '-q', '-k'], '-k on a polynomial that ratpoints reverses in case 3'),
    (['1 0 1', '5', '-q', '-s'], '-s: no Sturm step'),
    (['1 0 1', '5', '-q', '-S'], '-S: the Sturm step at the default depth'),
    (['1 0 1', '5', '-q', '-S', '5'], '-S 5: the Sturm step at depth 5'),
    (['1 0 1', '5', '-q', '-S', '0'], '-S 0: the Sturm step at depth 0'),
    (['1 0 1', '5', '-q', '-S', ' 3 '], '-S with blanks around its argument'),
    (['1 0 1', '5', '-q', '-S', '+3'], '-S +3'),
    (['1 0 1', '5', '-q', '-Sfoo', '3'], '-Sfoo 3 is -S 3'),
    (['1 0 1', '5', '-S', '-q'], '-S -q: -q is not the argument of -S'),
    (['1 0 1', '5', '-q', '-S', 'x'], '-S x: error 6'),
    (['1 0 1', '5', '-q', '-S', ''], '-S with an empty argument: error 6'),
    (['1 0 1', '5', '-q', '-S', '5x'], '-S 5x: error 6'),
    (['1 0 1', '5', '-q', '-S', '9223372036854775808'], '-S 2^63: error 6'),
    (['1 0 1', '5', '-q', '-S', '-5'], '-S -5: -5 is no argument but an unknown option, error 6'),
    (['1 0 1', '5', '-q', '-S', '5', '6'], '-S 5 6: the 6 is a word without -, error 6'),
    # the refusals of a form that is not squarefree (error 8), and -s on such forms
    (['1 2 1', '5', '-q'], 'a repeated factor: error 8, by the remainder chain'),
    (['0 0 1 1 1', '5', '-q'], 'even degree and c0 = c1 = 0: error 8, by the reversal check'),
    (['5 0', '5', '-q'], 'a leading zero that lowers the degree of the form: error 8'),
    (['1 2 0 0', '5', '-q', '-s', '-k'], 'two leading zeros that lower the degree: error 8'),
    (['1 2 1', '5'], 'error 8 without -q: the message after the report of ratpoints'),
    (['0 0 1', '5', '-v'], 'error 8 under -v: the message after the report of the library'),
    (['1 2 1', '3', '-q', '-s'], '-s: a repeated factor is searched'),
    (['1 0 -2 0 1', '3', '-q', '-s'], '-s: a repeated factor of degree 2 is searched'),
    (['0 0 1 1 1', '3', '-q', '-s'], '-s: even degree and c0 = c1 = 0 still refused'),
    (['0 0 1 1 1', '3', '-q', '-s', '-k'], '-s -k: even degree and c0 = c1 = 0 searched'),
    (['0 0 1 0 1', '3', '-q', '-k', '-s'], '-k -s: even degree and c0 = c1 = 0 searched'),
    (['1 2 1', '3', '-q', '-s', '-S'], '-s -S: the last one wins, the Sturm step, error 8'),
    (['1 2 1', '3', '-q', '-S', '-s'], '-S -s: the last one wins, no Sturm step'),
    (['1 2 1', '3', '-q', '-s', '-S', '3'], '-s -S 3: error 8'),
    (['1 2 1', '3', '-q', '-S', ' -1'], '-S with the argument -1 after a blank: no Sturm step'),
    # the options of the output: -x and -X (the exact check), -y and -Y (the pairs), -z and -Z (no
    # points printed), -1 (one point), -i and -I (the points at infinity); the last one wins
    (['1 0 1', '5', '-q', '-x'], '-x: the survivors of the sieve, (x : z)'),
    (['1 0 1', '5', '-q', '-x', '-n', '15', '-N', '30', '-p', '30'], '-x with the moduli pinned'),
    (['1 0 1', '5', '-q', '-x', '-X'], '-x -X: the last one wins, the points checked'),
    (['1 0 1', '5', '-q', '-xfoo', '-p', '30', '-N', '30'], '-xfoo is -x'),
    (['1 0 1', '5', '-q', '-y'], '-y: one point of each pair'),
    (['1 0 1', '5', '-q', '-y', '-Y'], '-y -Y: the last one wins'),
    (['1 0 1', '5', '-q', '-yes'], '-yes is -y'),
    (['1 0 1', '5', '-q', '-z'], '-z: no points printed'),
    (['1 0 1', '5', '-q', '-zap', '-Z'], '-zap -Z: the points printed'),
    (['1 0 1', '5', '-z'], '-z: the count in the report'),
    (['1 0 1', '5', '-z', '-i'], '-z -i: the points at infinity not counted'),
    (['1 0 1', '5', '-z', '-y'], '-z -y: the count of the pairs'),
    (['1 0 1', '5', '-z', '-1'], '-z -1: one point counted'),
    (['1 0 1', '5', '-q', '-1'], '-1: the first point, at infinity'),
    (['1 0 1', '5', '-q', '-1x'], '-1x is -1'),
    (['1 0 1', '5', '-q', '-1', '-i'], '-1 -i: the first point not at infinity'),
    (['1 0 1', '5', '-q', '-i'], '-i: no points at infinity'),
    (['1 0 1', '5', '-q', '-I', '-i'], '-I -i: the last one wins'),
    (['1 0 1', '5', '-q', '-i', '-I'], '-i -I: the last one wins'),
    (['2 0 4', '30', '-q', '-i'], '-i after a reversal: the caller\'s points at infinity dropped'),
    (['-1 0 9', '10', '-q', '-x', '-n', '15', '-N', '30', '-p', '30'],
     '-x after a reversal: (1 : 0) second'),
    (['-110398115831658495200097132973216241257761844312575 0 0 0 1', '10', '-q', '-x', '-p', '30',
      '-N', '30'], '-x where the Sturm step of the C program narrows its search region to the '
     'point at infinity: compared exactly with the C program under -s'),
    (['-1 0 9', '10', '-q', '-1', '-i'], '-1 -i after a reversal'),
    (['0 1 2', '40', '-q', '-1'], '-1: the point at infinity of the reversed polynomial'),
    (['1 0 1', '5', '-x', '-n', '15', '-N', '30', '-p', '30'], '-x in the report, pinned'),
    (['1 0 1', '5', '-y', '-j'], '-y -j in the report'),
    (['0 1 2', '40', '-z', '-y'], 'the report of a reversed polynomial'),
    (['1 0 0 6', '200', '-z'], 'the report: the divisors of the leading coefficient'),
    (['-2 0 0 1', '130', '-z'], 'the report: the squares'),
    # the formats and the strings
    (['1 0 1', '5', '-q', '-f', '%x %y %z\\n'], '-f with the three coordinates'),
    (['1 0 1', '5', '-q', '-f', '%'], '-f %: a percent sign at the end'),
    (['1 0 1', '5', '-q', '-f', '\\'], '-f \\: a backslash at the end'),
    (['1 0 1', '5', '-q', '-f', '%%%x'], '%% is no escape'),
    (['1 0 1', '5', '-q', '-f', '\\0\\a\\%\\\\\\t\\n'], 'the escapes, and \\0 \\a as they are'),
    (['1 0 1', '5', '-q', '-f', '%q%y'], 'an unknown conversion'),
    (['1 0 1', '5', '-q', '-f', '%y\\n', '-y'], '%y under -y prints itself'),
    (['1 0 1', '5', '-q', '-f', '%y\\n', '-x', '-p', '30', '-N', '30'], '%y under -x'),
    (['1 0 1', '5', '-q', '-f', '', '-fs', 'S', '-fm', 'M', '-fe', 'E'], 'an empty format'),
    (['1 0 1', '5', '-q', '-fm', '%x', '-fe', '%%'], 'no conversions in the strings'),
    (['1 0 1', '5', '-q', '-f', '-x'], '-f takes the next word, also -x'),
    (['1 0 1', '5', '-q', '-fe', '-y'], '-fe takes the next word, also -y'),
    (['1 0 1', '5', '-q', '-fsfoo', 'S'], '-fsfoo is -fs'),
    (['1 0 1', '5', '-q', '-f', 'a', '-f', 'b\\n'], 'the last -f wins'),
    (['-1 0 -1', '50', '-q', '-fs', 'S', '-fm', 'M', '-fe', 'E\\n'], 'no points: -fs and -fe'),
    (['1 0 126 0 441', '30', '-q', '-fs', 'S', '-fm', 'M', '-fe', 'E', '-y'],
     '-fs, -fm and -fe around several points'),
    (['-1 0 -1', '50', '-fs', 'S', '-fe', 'E\\n'], 'no points: -fs and -fe in the report'),
    (['1 0 1', '5', '-q', '-z', '-fs', 'S', '-fe', 'E'], '-z: -fs and -fe around no point'),
    (['1 0 1', '5', '-q', '-1', '-fs', '{', '-fe', '}\\n'], '-1 with -fs and -fe'),
    (['1 0 1', '5', '-q', '-f', '\u00e9%x\u20ac\\n'], 'a format in UTF-8'),
    (['1 0 1', '5', '-q', '-f'], '-f without its argument: error 6'),
    (['1 0 1', '5', '-q', '-fs'], '-fs without its argument: error 6'),
    (['1 0 1', '5', '-q', '-fm'], '-fm without its argument: error 6'),
    (['1 0 1', '5', '-q', '-fe'], '-fe without its argument: error 6'),
    (['1 0 1', '5', '-q', '-ffoo', 'x'], '-ffoo: error 6'),
    (['1 0 1', '5', '-q', '-f', '%\u00e9\\\u20ac%\u20ac%\\n'],
     'characters beyond ASCII after % and \\: as they are'),
    (['1 2 1', '5', '-q', '-x'], 'a form that is not squarefree and -x: error 8'),
    (['1 2 1', '5', '-x', '-fs', 'S'], 'error 8 without -q: no strings printed'),
    (['1 0 1', '5', '-q', '-x', '-p', 'x'], '-x before a malformed -p: error 6'),
    (['1 0 1', '5', '-q', '-x', '-g'], '-x before an unknown option: error 6'),
    (['1 0 1', '0', '-x'], 'bad height before -x: error 4'),
    # the search region: the intervals of -l and -u, the denominators of -dl and -du
    (['1 0 126 0 441', '200', '-l', '0', '-u', '1'],
     '-l -u: message 3, the points in [0, 1]'),
    (['1 0 126 0 441', '200', '-q', '-l', '0', '-u', '1'], '-l -u with -q'),
    (['-1 0 9', '10', '-q', '-u', '0.3333333333333333', '-l', '0.33333333333333337'],
     'two intervals whose doubles meet: joined, (1 : 0 : 3) between them passed over'),
    (['-1 0 9', '10', '-u', '0.3333333333333333', '-l', '0.33333333333333337'],
     'the join in the report: two intervals in message 3'),
    (['17 0 0 1', '300', '-q', '-dl', '4', '-du', '9'], '-dl -du: the denominators 4 to 9'),
    (['36 0 -49 0 14 0 -1', '100', '-l', '-2.5', '-u', '-1.5', '-l', '1.5', '-u', '2.5'],
     'two intervals in the report'),
    (['1 0 1', '10', '-z', '-l', '-0', '-u', '1e400'], '-0.000000 and inf in message 3'),
    (['1 0 1', '10', '-z', '-u', '-20'], 'a first -u below -H: [-inf, -20]'),
    (['1 0 1', '10', '-z', '-l', '20'], 'a last -l above H: [20, inf]'),
    (['1 0 1', '10', '-q', '-u', '1'], 'a first -u without -l'),
    (['1 0 1', '10', '-q', '-l', '1'], 'a last -l without -u'),
    (['1 0 1', '10', '-z', '-l', '1e400', '-u', '1e500'],
     '[inf, inf]: only the points at infinity'),
    (['1 0 1', '10', '-z', '-u', '-1e400'], '[-inf, -inf]: only the points at infinity'),
    (['1 0 1', '10', '-z', '-u', '0.74999999999999999', '-l', '0.75', '-u', '1'],
     'two intervals of the command line, one search interval'),
    (['1 0 1', '10', '-q', '-l', '1', '-u', '1'], '[1, 1] is an interval'),
    (['1 0 1', '10', '-q', '-l', '-1e-400', '-u', '1e-400'], 'ends that strtod reads as 0'),
    (['1 0 1', '10', '-q', '-l', '-0x1p-1075', '-u', '0x1.8p-1074'], 'tiny hexadecimal ends'),
    (['1 0 1', '10', '-q', '-l', ' 0x.8p1 ', '-u', '1.00000000000000000001\r'],
     'white space around ends, a hexadecimal end, one that is no double'),
    (['1 0 1', '10', '-q', '-l', '-inf', '-u', 'Infinity'], 'infinite ends'),
    (['1 0 1', '10', '-q', '-l', '-1', '-u', '-0', '-l', '1e-300', '-u', '1'],
     'intervals with -0 and a tiny end between them'),
    (['1 0 1', '10', '-v', '-l', '0', '-u', '1'], 'message 3 under -v'),
    (['1 0 1', '10', '-q', '-x', '-l', '0', '-u', '1', '-p', '30', '-N', '30'],
     '-x with an interval, pinned'),
    (['1 0 1', '10', '-q', '-x', '-l', '0', '-u', '1'], '-x with an interval'),
    (['1 0 126 0 441', '200', '-q', '-1', '-i', '-l', '0.5'], '-1 -i: a point outside not counted'),
    (['-1 0 9', '10', '-q', '-dl', '3', '-du', '3'], 'one denominator'),
    (['-1 0 9', '10', '-q', '-dl', '5', '-du', '3'], 'an empty range of denominators'),
    (['-1 0 9', '10', '-q', '-dl', '0', '-du', '0'], '-dl 0 -du 0: the defaults'),
    (['-1 0 9', '10', '-q', '-dl', '-5', '-du', '50'], '-dl below 1, -du above H'),
    (['-1 0 9', '10', '-q', '-du', '10'], '-du H: the reversal not suppressed'),
    (['-1 0 9', '10', '-q', '-du', '9'], '-du below H: no reversal'),
    (['0 1 0 2', '20', '-q', '-dl', '2'], '-dl 2: no reversal (case 3)'),
    (['0 0 1', '5', '-q', '-s', '-dl', '2'], '-s -dl 2: no reversal, so no error 8'),
    (['0 0 1', '5', '-q', '-s', '-l', '-1', '-u', '1'], '-s with an interval: no error 8'),
    (['0 0 1', '5', '-q', '-dl', '2'], 'the Sturm step refuses x^2 | F: error 8'),
    (['1 0 1', '5', '-q', '-dl', '2', '-dlx', '3', '-du', '4', '-du', '5'],
     'the last -dl and -du win, -dlx is -dl'),
    (['1 0 1', '5', '-q', '-dl', ' 2\r', '-du', '+4'], '-dl -du with white space and a sign'),
    (['1 0 1', '5', '-q', '-dl'], '-dl without its argument: error 6'),
    (['1 0 1', '5', '-q', '-du', 'x'], '-du x: error 6'),
    (['1 0 1', '5', '-q', '-du', '1.5'], '-du 1.5: error 6'),
    (['1 0 1', '5', '-q', '-dl', '9223372036854775808'], '-dl 2^63: error 6'),
    (['1 0 1', '5', '-q', '-l'], '-l without its argument: error 7'),
    (['1 0 1', '5', '-q', '-u'], '-u without its argument: error 7'),
    (['1 0 1', '5', '-q', '-l', 'x'], '-l x: error 7'),
    (['1 0 1', '5', '-q', '-u', 'nan'], '-u nan: error 7'),
    (['1 0 1', '5', '-q', '-l', '1', '-l', '2'], '-l -l: error 7'),
    (['1 0 1', '5', '-q', '-u', '1', '-u', '2'], '-u -u: error 7'),
    (['1 0 1', '5', '-q', '-l', '2', '-u', '1'], 'not ordered: error 7'),
    (['1 0 1', '5', '-q', '-u', '0.75', '-l', '0.75'], 'touching intervals: error 7'),
    (['1 0 1', '5', '-q', '-l', '1', '-u', '2', '-l', '1.5', '-u', '3'], 'overlapping: error 7'),
    (['1 0 1', '5', '-q', '-u', 'inf', '-l', 'inf'],
     'two infinities of one sign are equal: error 7'),
    (['1 0 1', '5', '-q', '-u', '1e-400', '-l', '1e-401'], 'two tiny ends count as equal: error 7'),
    (['1 0 1', '5', '-q', '-lfoo', '0', '-ux', '1'], '-lfoo is -l, -ux is -u'),
    (['1 0 1', '5', '-q', '-l', '1', '-u', '2', '-p', 'x'], 'an interval before a bad -p: error 6'),
    (['1 0 1', '5', '-q', '-p', 'x', '-l', 'x'], 'a bad -p before a bad -l: error 6'),
    (['1 0 1', '5', '-q', '-l', 'x', '-p', 'x'], 'a bad -l before a bad -p: error 7'),
    (['1 0 1', '5', '-q', '-f', '-l', '-l', '1'], '-f takes -l as its format'),
    (['1 0 1', '5', '-q', '-S', '-l', '1'], '-S followed by -l: -l is not its argument'),
    (['1 0 1', '5', '-q', '-g', '-l', '1'], 'an unknown option before -l: error 6'),
    (['1 0 1', '5', '-q', '-l', '1', '-u', '2', '-g'],
     'an interval before an unknown option: error 6'),
    (['1 0 1', '5', '-q', '-S', 'x', '-l', '1'], 'a malformed -S before -l: error 6'),
    (['x', '5', '-l', 'x'], 'bad coefficients before -l x: error 11 first'),
    (['1 0 1', '0', '-l', 'x'], 'bad height before -l x: error 4 first'),
    (['1 2 1', '5', '-q', '-l', '0', '-u', '1'], 'a form that is not squarefree with an interval'),
    *[(['1 0 1', '5', '-q', '-z'] + [w for i in range(n) for w in ['-l', str(2 * i), '-u',
       str(2 * i + 1)]], f'{n} intervals' + (': error 7' if n > 100 else ''))
      for n in (99, 100, 101)],
    # unknown options and other words
    (['1 0 1', '5', '-q', '-g'], '-g: error 6'),
    (['1 0 1', '5', '-q', '-w'], '-w: error 6'),
    (['1 0 1', '5', '-q', '-5'], '-5: error 6'),
    (['1 0 1', '5', '-q', '-'], '-: error 6'),
    (['1 0 1', '5', '-q', '--'], '--: error 6'),
    (['1 0 1', '5', '-q', '-d'], '-d: error 6'),
    (['1 0 1', '5', '-q', '-dx', '1'], '-dx: error 6'),
    (['1 0 1', '5', '-q', '-fx'], '-fx: error 6'),
    (['1 0 1', '5', '-q', ''], 'an empty word: error 6'),
    (['1 0 1', '5', '-q', 'foo'], 'a bare word: error 6'),
    (['1 0 1', '5', '-q', 'q'], 'q without -: error 6'),
    (['1 0 1', '5', '-q', '-é'.encode()], 'a non-ASCII option letter: error 6'),
    (['1 0 1', '5', '-q', b'-\xff'], 'a byte that is not UTF-8 as option letter: error 6'),
    (['1 0 1', '5', '-q', '-fé'.encode()], '-f and a non-ASCII letter: error 6'),
]


# Searches at a large height that both programs stop at once (-1): the polynomial is not reversed
# and has a point at infinity (odd degree, or a leading coefficient that is a square), which the
# search delivers before the sieve; chosen by hand, since a stop inside the sieve at such a height
# would not end in ratpoints-lean, which lists the denominators of a search up front.
STOP_CASES = [
    (['1 0 1', '1000000000000', '-q', '-1'], '-1 at a large height: (1 : 1 : 0) at once'),
    (['3 2 -1 12', '1000000000000', '-q', '-1'], '-1 at a large height, odd degree: (1 : 0 : 0)'),
]


# C white space: the space and the characters from tab to carriage return.
SPACE = ' \t\n\x0b\x0c\r'
LONG_OPTS = 'pFtnNRAP'
DOUBLE_OPTS = 'rUCQW'


def random_digits(rng, alphabet, lengths=(0, 1, 1, 2, 3)):
    return ''.join(rng.choice(alphabet) for _ in range(rng.choice(lengths)))


def random_double(rng):
    """A word for strtod: a decimal or hexadecimal floating constant, an infinity or a NaN, often
    malformed, with white space and a sign at times."""
    p = []
    if rng.random() < 0.2:
        p.append(rng.choice(SPACE) * rng.randint(1, 2))
    if rng.random() < 0.4:
        p.append(rng.choice('+-'))
    k = rng.random()
    if k < 0.15:
        p.append(rng.choice(['inf', 'INF', 'Inf', 'infinity', 'Infinity', 'INFINITY', 'iNfInItY',
                             'infinit', 'infx', 'nan', 'NaN', 'NAN', 'nan(1)', 'nan()', 'nan(',
                             'in', 'i', 'infinityy']))
    else:
        hexa = k < 0.45
        if hexa:
            p.append(rng.choice(['0x', '0X', '0x', 'x', '0', '00x']))
        digits = '0123456789abcdefABCDEF' if hexa else '0123456789'
        m = random_digits(rng, digits)
        if rng.random() < 0.5:
            m += '.' + random_digits(rng, digits, (0, 0, 1, 2))
        p.append(m)
        if rng.random() < 0.5:
            e = rng.choice('pPeE' if hexa else 'eEpP')
            if rng.random() < 0.4:
                e += rng.choice('+-')
            e += random_digits(rng, '0123456789', (0, 1, 1, 2, 3))
            p.append(e)
    if rng.random() < 0.15:
        p.append(rng.choice(['x', '.', 'e', ' 1', '\t', '5', 'f', 'L', ',', '+', 'p1']))
    if rng.random() < 0.2:
        p.append(rng.choice(SPACE))
    return ''.join(p)


def random_long(rng):
    """A word for strtol in base 10, often malformed or out of the range of a long."""
    p = []
    if rng.random() < 0.2:
        p.append(rng.choice(SPACE))
    if rng.random() < 0.4:
        p.append(rng.choice(['+', '-', '+', '-', '--', '+-', '- ']))
    if rng.random() < 0.3:
        p.append(rng.choice(['9223372036854775807', '9223372036854775808', '9223372036854775806',
                             '09223372036854775807', '18446744073709551616',
                             '99999999999999999999', '922337203685477580']))
    else:
        p.append(random_digits(rng, '0123456789', (0, 1, 1, 2, 5)))
    if rng.random() < 0.15:
        p.append(rng.choice(['x', '.0', 'e3', ' 1', '\t', 'L', '_000', ',']))
    if rng.random() < 0.2:
        p.append(rng.choice(SPACE) * rng.randint(1, 2))
    return ''.join(p)


def random_coefficients(rng):
    """A coefficient list of 0 to 103 words, valid in half of the cases, with C white space."""
    n = rng.choice([0, 1, 1, 2, 3, 4, 5, 99, 100, 101, 102, 103])
    valid = rng.random() < 0.5
    ws = []
    for _ in range(n):
        w = ''
        if rng.random() < 0.3:
            w += rng.choice(['+', '-'] if valid else ['+', '-', '+', '-', '--', '-+'])
        w += random_digits(rng, '0123456789', (1, 1, 2, 3, 25) if valid else (0, 1, 1, 2, 3, 25))
        if not valid and rng.random() < 0.05:
            w += rng.choice(['x', '.5', ',', '-', '+1', 'e2', '_0'])
        ws.append(w)
    seps = [rng.choice([' ', ' ', '  ', '\t', '\n', '\x0b', '\x0c', '\r', ' \r\n'])
            for _ in range(len(ws) + 1)]
    s = ''.join(seps[i] + ws[i] for i in range(len(ws))) + seps[-1]
    return s if rng.random() < 0.8 else s.strip(SPACE)


# Formats and strings for -f, -fs, -fm and -fe: conversions, escapes, a percent sign or a backslash
# at the end, words that look like options, and characters beyond ASCII in UTF-8, also after % and
# a backslash, which main.c reads byte by byte (main.c:157-186 the format, main.c:952-968 the
# strings) and ratpoints-lean character by character (the Lean runtime decodes the arguments, so
# that bytes that are not UTF-8 are a deviation).
FORMATS = ['%x %y %z\\n', '(%x : %z)\\n', '%x\\t%y\\n', '%', '\\', '%%', '%%%x', '\\%\\\\',
           '\\0\\a', '', '[%x/%z]', '%q%y%', '-x', '-q', 'x\\n', '\u00e9%x\u20ac\\n', ' %z ',
           '\\n', '%x\\', '%y', '%\u00e9', '\\\u20ac', '%\u20ac%']


def random_options(rng):
    """One to three options of ratpoints, some unknown, some with a random argument."""
    letters = 'pFtnNRAPrUCQWqvjJlukKxXyYzZ1iIsSfdgwbcehmo5-'
    opts = []
    for _ in range(rng.choice([1, 1, 2, 3])):
        if rng.random() < 0.05:
            opts.append(rng.choice(['', 'q', 'foo', '-']))
            continue
        o = '-' + rng.choice(letters)
        if rng.random() < 0.25:
            o += rng.choice(['s', 'm', 'e', 'l', 'u', 'x', 'q', 'uiet', '1'])
        opts.append(o)
        if (o[1] in LONG_OPTS or o[1] == 'd' and o[2:3] in ('l', 'u')) and rng.random() < 0.9:
            opts.append(random_long(rng))
        elif o[1] in 'lu' and rng.random() < 0.9:
            opts.append(random_double(rng))
        elif o[1] in DOUBLE_OPTS and rng.random() < 0.9:
            opts.append(random_double(rng))
        elif o[1] == 'S' and rng.random() < 0.5:
            opts.append(random_long(rng))
        elif o[1] == 'f' and rng.random() < 0.9:
            opts.append(rng.choice(FORMATS))
    return opts


def random_output_options(rng):
    """Options of the output for a search: each of -x -X -y -Y -z -Z -1 -i -I at times, -q in most
    cases and -v at times, a format and strings at times, at times the parameters that pin the
    moduli for -x (-p 30 -N 30), and with -x at times -s, so that the survivors over the whole of
    [-H, H] are compared, where the polynomial may be negative."""
    opts = [o for o in ['-x', '-X', '-y', '-Y', '-z', '-Z', '-1', '-i', '-I']
            if rng.random() < 0.15]
    rng.shuffle(opts)
    if rng.random() < 0.8:
        opts.append('-q')
    elif rng.random() < 0.3:
        opts.append('-v')
    for o in ['-f', '-fs', '-fm', '-fe']:
        if rng.random() < 0.15:
            opts += [o, rng.choice(FORMATS)]
    if rng.random() < 0.3:
        opts += ['-p', '30', '-N', '30']
    if '-x' in opts and rng.random() < 0.3:
        opts.append('-s')
    return opts


def random_output_words(rng):
    """One to five options of the output, each of -x -X -y -Y -z -Z -1 -i -I -q -v at times with
    letters after it, or one of -f -fs -fm -fe with a format or a string."""
    opts = []
    for _ in range(rng.randint(1, 5)):
        if rng.random() < 0.5:
            opts.append('-' + rng.choice('xXyYzZ1iIqv') + rng.choice(['', '', '', 'foo']))
        else:
            opts += ['-f' + rng.choice(['', 's', 'm', 'e']), rng.choice(FORMATS)]
    return opts


def random_command_lines(rng):
    """Eight random command lines: two coefficient lists, three arguments of tuning options, a
    height, an option list and options of the output; the height bound is at most 5, or an option
    that fails follows. The option list searches a squarefree form or one that is not, so that the
    switch of the Sturm step and the depth that -S reads decide between error 8 and the points; the
    options of the output come after a curve with points, among them points at infinity."""
    return [[random_coefficients(rng), '1', '-g'],
            ['1 0 1', '1', '-q', '-r', random_double(rng)],
            ['1 0 1', '1', '-q', '-W', random_double(rng)],
            ['1 0 1', '1', '-q', '-p', random_long(rng)],
            ['1 0 1', random_long(rng), '-g'],
            [random_coefficients(rng), '1', '-g'],
            [rng.choice(['1 0 1', '1 2 1']), '2', '-q', *random_options(rng)],
            [rng.choice(['1 0 1', '0 1 2', '1 0 126 0 441', '-2 0 0 1', '1 2 3 4']),
             str(rng.randint(1, 5)), *random_output_words(rng)]]


# Search regions: words for the ends, sorted by their values (end_fraction), and the curves they are
# tried on.
INF = float('inf')
NEAR_THIRD = ['0.3333333333333333', '0.33333333333333337', '0.33333333333333331',
              '0.333333333333333314829616256247', '0.33333333333333334']
POINT_RICH = ['1 0 126 0 441', '-2 0 0 1', '1 1 1 1 0', '1 2 3 4 5 6 7', '-1 0 9', '0 1 1',
              '36 0 -49 0 14 0 -1', '17 0 0 1', '1 0 1', '0 1 0 2', '-4 0 5 0 -1', '1 0 0 6']


def end_fraction(word):
    """The value of an end word for sorting: a Fraction, or +-inf for an infinity."""
    w = word.strip()
    sign = -1 if w.startswith('-') else 1
    v = w.lstrip('+-')
    if v.lower() in ('inf', 'infinity'):
        return sign * INF
    if v.lower().startswith('0x'):
        m, _, e = v[2:].lower().partition('p')
        ip, _, fp = m.partition('.')
        num = int((ip + fp) or '0', 16)
        return sign * Fraction(num) * Fraction(2) ** (int(e or '0') - 4 * len(fp))
    f = Fraction(v)
    return sign * (INF if f >= 2 ** 1024 - 2 ** 970 else f)


def random_end(rng, H):
    """A word for an end of a search interval, for the height H: a small decimal, a fraction with
    many digits, a hexadecimal constant, an integer near +-H, an infinity, a number beyond the
    doubles, a tiny one, -0, a word near 1/3 whose doubles meet, or the repr of a quotient of small
    integers; with white space at times."""
    k = rng.random()
    if k < 0.3:
        w = str(round(rng.uniform(-12, 12), rng.choice([0, 1, 2, 3, 6])))
    elif k < 0.4:
        w = '%.20g' % rng.uniform(-3, 3)
    elif k < 0.5:
        w = rng.choice(['', '-']) + rng.choice(['0x1.8p-1', '0x.4p3', '0X1P-2', '0x3p0',
                                                '0x1.fffffffffffffp1', '0x1p-1075',
                                                '0x1.0000000000001p-1074'])
    elif k < 0.6:
        w = str(rng.choice([-1, 1]) * (H + rng.randint(-2, 2)))
    elif k < 0.67:
        w = rng.choice(['inf', '-inf', 'Infinity', '-INF', '1e400', '-1e400', '1e30', '-1e30'])
    elif k < 0.75:
        w = rng.choice(['1e-400', '-1e-400', '0', '-0', '0.0', '-0x0p0', '1e-300', '-2e-320'])
    elif k < 0.85:
        w = rng.choice(['', '-']) + rng.choice(NEAR_THIRD)
    else:
        w = repr(rng.randint(-20, 20) / rng.randint(1, 9))
    if rng.random() < 0.05:
        w = rng.choice([' ', '\t']) + w + rng.choice(['', '\r', ' '])
    return w


def random_intervals(rng, H):
    """The options -l and -u of one to five random intervals: their ends sorted most of the time
    (unsorted ones give error 7), at times the same word as the upper end of one interval and the
    lower end of the next (error 7) or words whose doubles meet (joined); the first -l and the last
    -u left out at times."""
    k = rng.choice([1, 1, 1, 2, 2, 3, 5])
    ends = [random_end(rng, H) for _ in range(2 * k)]
    if rng.random() < 0.85:
        ends.sort(key=end_fraction)
    if k > 1 and rng.random() < 0.15:
        j = rng.randrange(k - 1)
        if rng.random() < 0.5:
            ends[2 * j + 2] = ends[2 * j + 1]
        else:
            ends[2 * j + 1], ends[2 * j + 2] = '0.3333333333333333', '0.33333333333333337'
            ends.sort(key=end_fraction)
    opts = []
    for j in range(k):
        if not (j == 0 and rng.random() < 0.2):
            opts += ['-l', ends[2 * j]]
        if not (j == k - 1 and opts and rng.random() < 0.2):
            opts += ['-u', ends[2 * j + 1]]
    return opts


def random_denominators(rng, H):
    """Options -dl and -du of a random range of denominators: a lower bound, an upper one or both,
    an empty range, one denominator, bounds beyond 1 and H and below 1."""
    k = rng.random()
    if k < 0.25:
        return ['-dl', str(rng.randint(-2, H + 1))]
    if k < 0.5:
        return ['-du', str(rng.randint(-2, H + 2))]
    if k < 0.65:
        b = rng.randint(1, H)
        return ['-dl', str(b), '-du', str(b)]
    lo, hi = rng.randint(-1, H), rng.randint(-1, H + 3)
    return ['-dl', str(lo), '-du', str(hi)]


def random_search_options(rng):
    """Options of the search and of the output for a search with a region: -q most of the time, the
    report or -v at times, and at times -k, -s, -S with a depth, -x with or without the moduli
    pinned, -1, -i, -y, -z."""
    opts = ['-q'] if rng.random() < 0.7 else (['-v'] if rng.random() < 0.2 else [])
    for o in ['-k', '-s', '-1', '-i', '-y', '-z']:
        if rng.random() < 0.08:
            opts.append(o)
    if rng.random() < 0.1:
        opts += ['-S', str(rng.choice([0, 1, 2, 5, 20, 55, 60]))]
    if rng.random() < 0.1:
        opts.append('-x')
        if rng.random() < 0.6:
            opts += ['-p', '30', '-N', '30']
    return opts


BIG_HEIGHTS = [10 ** 6, 10 ** 9, 10 ** 12, 2 ** 53 + 1, 2 ** 62, 2 ** 63 - 1]


def exact_word(rng, v):
    """A word that denotes the double v exactly: its hexadecimal form or its decimal expansion."""
    return v.hex() if rng.random() < 0.5 else format(Decimal(v), 'f')


def pythagorean_point(rng, H):
    """A point (m^2 - n^2 : m^2 + n^2 : 2 m n) of y^2 = x^2 + 1 of height at most H, m > n coprime
    and of opposite parity, with a denominator 2 m n between about H / 10 and H, as (x, z); None if
    none is found."""
    for _ in range(20):
        n = rng.randint(max(1, math.isqrt(H // 20)), math.isqrt(H // 5))
        m = n + 1 + 2 * rng.randint(0, n // 2)
        while math.gcd(m, n) != 1:
            m += 2
        if 2 * m * n <= H and m * m - n * n <= H:
            return m * m - n * n, 2 * m * n
    return None


def random_big_region(rng, c):
    """A search of the polynomial with the coefficient list c at a large height in a narrow search
    region, so that it sifts few numerators, without -1: a narrow range of denominators b, ...,
    b + j and one interval, with -q and at times -x with the moduli pinned (-p 30 -N 30), so that
    every survivor is compared. The interval lies around a random x = a / b, with the repr of
    doubles as its ends, which are rarely exact; or has ends that are exact doubles L / 2^e whose
    products with b are integers (2^e divides b), so that numerators at the ends lie in the search
    region and a bound of the numerators computed too narrow shows; or lies at one end of the range
    [-H, H] of the numerators at b, beyond it; or, on y^2 = x^2 + 1, its ends are the doubles next
    but one to the x-coordinate of a point (m^2 - n^2 : m^2 + n^2 : 2 m n) of large height, at its
    denominator."""
    H = rng.choice(BIG_HEIGHTS)
    k = rng.random()
    point = pythagorean_point(rng, H) if k >= 0.75 else None
    if point:
        c, (a, b) = '1 0 1', point
        v = float(Fraction(a, b))
        lo = math.nextafter(math.nextafter(v, -math.inf), -math.inf)
        hi = math.nextafter(math.nextafter(v, math.inf), math.inf)
        ends = ['-l', exact_word(rng, lo), '-u', exact_word(rng, hi)]
    elif 0.3 <= k < 0.55:
        e = rng.randint(0, (H // 50).bit_length() - 1)
        s = rng.randint(1, 50)
        b, j = s << e, rng.randint(0, 40)
        L = rng.randint(-min(2 ** 53 - 1, H // s), min(2 ** 53 - 1, H // s) - j)
        ends = ['-l', exact_word(rng, L / 2 ** e), '-u', exact_word(rng, (L + j) / 2 ** e)]
    elif 0.55 <= k < 0.75:
        b = rng.randint(1, H)
        lo = float(Fraction(H - rng.randint(0, 2000), b))
        hi = float(Fraction(H + rng.randint(1, 2000), b))
        if rng.random() < 0.5:
            lo, hi = -hi, -lo
        ends = ['-l', exact_word(rng, lo), '-u', exact_word(rng, hi)]
    else:
        b = rng.randint(1, H)
        x = Fraction(rng.randint(-H, H), b)
        w = Fraction(rng.randint(1, 2000), b + 20)
        ends = ['-l', repr(float(x - w)), '-u', repr(float(x + w))]
    x_opts = ['-x', '-p', '30', '-N', '30'] if rng.random() < 0.4 else []
    return [c, str(H), '-q', '-dl', str(b), '-du', str(min(H, b + rng.randint(0, 20))), *ends,
            *x_opts]


def random_region_line(rng):
    """A search with a random search region: a random polynomial or a point-rich curve at a small
    height with random intervals, a random range of denominators or both, and random options; or,
    one time in ten, a search at a large height in a narrow search region (random_big_region)."""
    if rng.random() < 0.6:
        c = ' '.join(str(rng.randint(-10, 10)) for _ in range(rng.randint(2, 9)))
    else:
        c = rng.choice(POINT_RICH)
    if rng.random() < 0.1:
        return random_big_region(rng, c)
    H = rng.randint(1, 60)
    k = rng.random()
    region = (random_intervals(rng, H) if k < 0.45 else random_denominators(rng, H) if k < 0.7
              else random_intervals(rng, H) + random_denominators(rng, H))
    return [c, str(H), *region, *random_search_options(rng)]

