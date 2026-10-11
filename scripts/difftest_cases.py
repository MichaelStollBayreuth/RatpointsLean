"""The command lines of the suites errors and fuzz of scripts/difftest.py.

CASES holds hand-written command lines for the checks that main.c makes on the coefficients, the
height and the options, for the options of the search and for the refusals of a form that is not
squarefree, each with a note; random_command_lines gives random ones, with words that the readers
of numbers of main.c accept or refuse in many ways. An argument is a str or, for a byte string that
is not UTF-8, bytes. A height that a search could not finish (such as 2^63 - 1) is always followed
by an option that fails, so that neither program searches.
"""

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
    (['1 0 1', '5'], 'no -q: ratpoints prints its report, ratpoints-lean only the points'),
    (['1 0 1', '5', '-v'], '-v alone: ratpoints prints the report of the library'),
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
    # the options that ratpoints-lean does not support yet
    (['1 0 1', '5', '-q', '-l', '0', '-u', '1'], '-l -u: unsupported'),
    (['1 0 1', '5', '-q', '-u', '1'], '-u: unsupported'),
    (['1 0 1', '5', '-q', '-dl', '2'], '-dl: unsupported'),
    (['1 0 1', '5', '-q', '-du', '2'], '-du: unsupported'),
    (['1 0 1', '5', '-q', '-dlx', '2'], '-dlx is -dl: unsupported'),
    (['1 0 1', '5', '-q', '-x'], '-x: unsupported'),
    (['1 0 1', '5', '-q', '-X'], '-X: unsupported'),
    (['1 0 1', '5', '-q', '-y'], '-y: unsupported'),
    (['1 0 1', '5', '-q', '-Y'], '-Y: unsupported'),
    (['1 0 1', '5', '-q', '-1'], '-1: unsupported'),
    (['1 0 1', '5', '-q', '-i'], '-i: unsupported'),
    (['1 0 1', '5', '-q', '-I'], '-I: unsupported'),
    (['1 0 1', '5', '-q', '-f', '%x'], '-f: unsupported'),
    (['1 0 1', '5', '-q', '-fs', 'a'], '-fs: unsupported'),
    (['1 0 1', '5', '-q', '-fm', 'a'], '-fm: unsupported'),
    (['1 0 1', '5', '-q', '-fe', 'a'], '-fe: unsupported'),
    (['1 0 1', '5', '-q', '-z'], '-z: unsupported'),
    (['1 0 1', '5', '-q', '-Z'], '-Z: unsupported'),
    (['1 0 1', '5', '-q', '-xfoo'], '-xfoo is -x: unsupported, named as written'),
    (['1 0 1', '5', '-q', '-l'], '-l without its argument: C error 7, unsupported here'),
    (['1 0 1', '5', '-q', '-l', 'x'], '-l x: C error 7, unsupported here'),
    (['1 0 1', '5', '-q', '-f'], '-f without its argument: C error 6, unsupported here'),
    (['1 0 1', '5', '-q', '-dl'], '-dl without its argument: C error 6, unsupported here'),
    (['1 0 1', '5', '-q', '-x', '-p', 'x'], '-x before a malformed -p: unsupported first'),
    (['1 0 1', '5', '-q', '-p', 'x', '-x'], 'a malformed -p before -x: error 6 first'),
    (['1 0 1', '5', '-q', '-g', '-x'], 'an unknown option before -x: error 6 first'),
    (['1 0 1', '5', '-q', '-x', '-g'], '-x before an unknown option: unsupported first'),
    (['x', '5', '-x'], 'bad coefficients before -x: error 11 first'),
    (['1 0 1', '0', '-x'], 'bad height before -x: error 4 first'),
    (['1 0 1', '5', '-q', '-S', 'x', '-x'], 'a malformed -S before -x: error 6 first'),
    (['1 0 1', '5', '-q', '-S', '-x'], '-S followed by -x: -x is not its argument, unsupported'),
    (['1 2 1', '5', '-q', '-x'], 'a form that is not squarefree and -x: unsupported first'),
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
        if o[1] in LONG_OPTS and rng.random() < 0.9:
            opts.append(random_long(rng))
        elif o[1] in DOUBLE_OPTS and rng.random() < 0.9:
            opts.append(random_double(rng))
    return opts


def random_command_lines(rng):
    """Seven random command lines: two coefficient lists, three arguments of tuning options, a
    height and an option list; the height bound is 1 or 2, or an option that fails follows."""
    return [[random_coefficients(rng), '1', '-g'],
            ['1 0 1', '1', '-q', '-r', random_double(rng)],
            ['1 0 1', '1', '-q', '-W', random_double(rng)],
            ['1 0 1', '1', '-q', '-p', random_long(rng)],
            ['1 0 1', random_long(rng), '-g'],
            [random_coefficients(rng), '1', '-g'],
            ['1 0 1', '2', '-q', *random_options(rng)]]
