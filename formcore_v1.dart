// FormCoreJS (https://github.com/moonad/FormCoreJS) Dart port.
//
// v1: FormCore typechecker and parser i.e. the FormCore.js file at https://github.com/moonad/FormCoreJS
//
// environment:
//   sdk: ">=2.15.0-82.0.dev <3.0.0"
//
// No dependencies.

void main() {
  const code = """
Bool : * =
  %self(P: @(self: Bool) *)
  @(true: (P true))
  @(false: (P false))
  (P self);

true : Bool =
  #P #t #f t;

false : Bool =
  #P #t #f f;

not : @(x: Bool) Bool =
  #x (((x #self Bool) false) true);

Equal : @(A: *) @(a: A) @(b: A) * =
  #A #a #b
  %self(P: @(b: A) @(self: (((Equal A) a) b)) *)
  @(refl: ((P a) ((refl A) a)))
  ((P b) self);

refl : %(A: *) %(a: A) (((Equal A) a) a) =
  #A #x #P #refl refl;

double_negation_theorem : @(b: Bool) (((Equal Bool) (not (not b))) b) =
  #b (((b #self (((Equal Bool) (not (not self))) self))
    ((refl Bool) true))
    ((refl Bool) false));

main : Bool =
  (not false);
""";
  final defs = parse(
    code: code,
  );
  print(
    show_defs(
      defs,
    ),
  );
  reportDefs(
    defs: defs,
  );
}

// Drivers.

Defs parse({
  required final String code,
}) =>
    parse_defs(
      code: code,
    );

void report({
  required final String code,
}) {
  final defs = () {
    try {
      return parse_defs(
        code: code,
      );
    } on Object catch (_) {
      print("Exception encountered while parsing defs.");
      rethrow;
    }
  }();
  reportDefs(
    defs: defs,
  );
}

void reportDefs({
  required final Defs defs,
}) {
  bool wrong = false;
  for (final name in defs.entries) {
    try {
      _typecheck(
        name.value.type,
        const _TermTypImpl(),
        defs,
        _nil(),
      );
      _typecheck(
        name.value.term,
        name.value.type,
        defs,
        _nil(),
      );
    } on Err catch (err) {
      wrong = true;
      print(_show_error(err, name.key));
    }
  }
  if (!wrong) {
    print("All terms check.");
  } else {
    // Typechecking did not succeed for all terms.
  }
}

Defs parse_defs({
  required final String code,
}) {
  final defs = <String, Def>{};
  _makeFormCoreParser(code)._parse_defs(defs);
  return defs;
}

Term parse_term({
  required final String code,
}) =>
    _makeFormCoreParser(code).parse_term()(_nil());

String show_defs(
  final Defs defs,
) {
  String str = "";
  for (final e in defs.entries) {
    // ignore: use_string_buffers
    str += e.key + ": " + _show(e.value.type, 0) + _show(e.value.term, 0) + ";\n";
  }
  return str;
}

// Models.

abstract class Term {}

abstract class TermVaar implements Term {
  String get name;

  int get indx;
}

abstract class TermRef implements Term {
  String get name;
}

abstract class TermTyp implements Term {}

abstract class TermAll implements Term {
  bool get eras;

  String get self;

  String get name;

  Term get bind;

  Term Function(Term self_var, Term name_var) get body;
}

abstract class TermLam implements Term {
  String get name;

  Term Function(Term name_var) get body;
}

abstract class TermApp implements Term {
  Term get func;

  Term get argm;
}

abstract class TermLet implements Term {
  String get name;

  Term get expr;

  Term Function(Term) get body;
}

abstract class TermDef implements Term {
  String get name;

  Term get expr;

  Term Function(Term) get body;
}

abstract class TermAnn implements Term {
  bool get done;

  Term get expr;

  Term get type;
}

abstract class TermNat implements Term {
  BigInt get natx;
}

abstract class TermChr implements Term {
  String get chrx;
}

abstract class TermStr implements Term {
  String get strx;
}

abstract class Liist {
  int get size;
}

abstract class LiistNil implements Liist {}

abstract class LiistExt implements Liist {
  Ctx get head;

  Liist get tail;
}

abstract class Err implements Exception {
  Term get term;

  Liist get ctx;

  String get msg;
}

typedef Defs = Map<String, Def>;

abstract class Def {
  Term get type;

  Term get term;
}

abstract class Ctx {
  String get name;

  Term get type;
}

extension TermMatcherExtension on Term {
  Z match<Z>({
    required final Z Function(TermVaar) vaar,
    required final Z Function(TermRef) ref,
    required final Z Function(TermTyp) typ,
    required final Z Function(TermAll) all,
    required final Z Function(TermLam) lam,
    required final Z Function(TermApp) app,
    required final Z Function(TermLet) let,
    required final Z Function(TermDef) def,
    required final Z Function(TermAnn) ann,
    required final Z Function(TermNat) nat,
    required final Z Function(TermChr) chr,
    required final Z Function(TermStr) str,
  }) {
    final _ = this;
    if (_ is TermVaar) return vaar(_);
    if (_ is TermRef) return ref(_);
    if (_ is TermTyp) return typ(_);
    if (_ is TermAll) return all(_);
    if (_ is TermLam) return lam(_);
    if (_ is TermApp) return app(_);
    if (_ is TermLet) return let(_);
    if (_ is TermDef) return def(_);
    if (_ is TermAnn) return ann(_);
    if (_ is TermNat) return nat(_);
    if (_ is TermChr) return chr(_);
    if (_ is TermStr) return str(_);
    throw Exception("Invalid State");
  }
}

extension LiistMatcherExtension on Liist {
  Z match<Z>({
    required final Z Function(LiistNil) nil,
    required final Z Function(LiistExt) ext,
  }) {
    final _ = this;
    if (_ is LiistNil) return nil(_);
    if (_ is LiistExt) return ext(_);
    throw Exception("Invalid State");
  }
}

/// Finds first value satisfying `cond` in a list
R _list_find<R>(
  final Liist list,
  final bool Function(Ctx, int indx) cond,
  final int indx,
  final int skip,
  final R Function(Ctx, int) found,
  final R Function() notFound,
) =>
    list.match(
      nil: (final a) => notFound(),
      ext: (final a) {
        if (cond(a.head, indx)) {
          if (skip == 0) {
            return found(a.head, indx);
          } else {
            return _list_find(
              a.tail,
              cond,
              indx + 1,
              skip - 1,
              found,
              notFound,
            );
          }
        } else {
          return _list_find(
            a.tail,
            cond,
            indx + 1,
            skip,
            found,
            notFound,
          );
        }
      },
    );

// Syntax
// ======

String _show_string(
  final String str,
) {
  String out = "";
  for (int i = 0; i < str.length; i++) {
    final cur = str[i];
    if (cur == "\\" || cur == '"' || cur == "'") {
      out += "\\" + cur;
    } else if (cur.codeUnitAt(0) >= ' '.codeUnitAt(0) && cur.codeUnitAt(0) <= "~".codeUnitAt(0)) {
      out += cur;
    } else {
      out += "\\u{" + str.codeUnitAt(i).toRadixString(16) + "}";
    }
  }
  return out;
}

String _show(
  final Term term,
  final int depth,
) =>
    term.match(
      vaar: (final a) => a.name,
      ref: (final a) => a.name,
      typ: (final a) => "*",
      all: (final a) {
        final bind = () {
          if (a.eras) {
            return "%";
          } else {
            return "@";
          }
        }();
        final self = a.self;
        final name = a.name;
        final type = _show(a.bind, depth);
        final body = _show(
          a.body(
            _TermVaarImpl(name: self, indx: 0),
            _TermVaarImpl(name: name, indx: 0),
          ),
          depth + 2,
        );
        return bind + self + "(" + name + ":" + type + ") " + body;
      },
      lam: (final a) {
        final name = a.name;
        final body = _show(a.body(_TermVaarImpl(name: name, indx: 0)), depth + 1);
        return "#" + name + " " + body;
      },
      app: (final a) {
        final func = _show(a.func, depth);
        final argm = _show(a.argm, depth);
        return "(" + func + " " + argm + ")";
      },
      let: (final a) {
        final name = a.name;
        final expr = _show(a.expr, depth);
        final body = _show(a.body(_TermVaarImpl(name: name, indx: 0)), depth + 1);
        return "!" + name + "=" + expr + ";" + body;
      },
      def: (final a) {
        final name = a.name;
        final expr = _show(a.expr, depth);
        final body = _show(a.body(_TermVaarImpl(name: name, indx: 0)), depth + 1);
        return "\$" + name + "=" + expr + ";" + body;
      },
      ann: (final a) {
        final expr = _show(a.expr, depth);
        // final type = show(a.type, depth);
        // return "{" + expr + ":" + type + "}";
        return expr;
      },
      nat: (final a) => a.natx.toRadixString(10),
      chr: (final a) => "'" + _show_string(a.chrx) + "'",
      str: (final a) => '"' + _show_string(a.strx) + '"',
    );

String _show_context(
  final Liist ctx,
  final String text,
) =>
    ctx.match(
      ext: (final a) {
        final name = a.head.name;
        final type = _show(a.head.type, 0);
        if (name.isNotEmpty) {
          return _show_context(a.tail, "- " + name + ": \x1b[2m" + type + "\x1b[0m\n" + text);
        } else {
          return _show_context(a.tail, text);
        }
      },
      nil: (final a) => text,
    );

String _show_error(
  final Err err,
  final String def_name,
) {
  String str = "";
  str += "\x1b[1mError on '" + def_name + "':\x1b[0m\n";
  str += err.msg + "\n";
  str += "Expression: \x1b[2m" + _show(err.term, 0) + "\x1b[0m\n";
  if (err.ctx is! LiistNil) {
    str += "Context:\n";
    str += _show_context(err.ctx, "");
  }
  return str;
}

_FormCoreParser _makeFormCoreParser(
  final String source,
) =>
    _FormCoreParser(
      source //
          .split("\n")
          .where((final a) {
        if (a.length >= 2) {
          return a.substring(0, 2) != "//";
        } else {
          return false;
        }
      }).join("\n"),
    );

class _FormCoreParser {
  /// Code without any comments.
  final String code;
  int indx = 0;

  _FormCoreParser(
    final this.code,
  );

  bool is_name(
    final String chr,
  ) {
    final val = chr.codeUnitAt(0);
    return val >= 46 && val <= 47 || // ./
        val >= 48 && val < 58 || // 0-9
        val >= 65 && val < 91 || // A-Z
        val >= 95 && val < 96 || // _
        val >= 97 && val < 123; // a-z
  }

  String parse_name() {
    if (indx < code.length && is_name(code[indx])) {
      return code[indx++] + parse_name();
    } else {
      return "";
    }
  }

  void parse_spaces() {
    for (;;) {
      if (indx >= code.length) {
        break;
      } else if (" \n\r\t\v\f".contains(code[indx])) {
        indx++;
      } else {
        break;
      }
    }
  }

  void parse_char(
    final String chr,
  ) {
    parse_spaces();
    if (indx >= code.length) {
      throw Exception("Unexpected eof.");
    } else if (code[indx] != chr) {
      throw Exception(
        "Expected'" + chr + "', found " + code[indx] + ' at ' + indx.toString() + ".",
      );
    }
    ++indx;
  }

  String parse_tokn() {
    if (indx >= code.length) {
      throw Exception("Unexpected eof");
    } else if (code[indx] == "\\") {
      final esc = code[++indx];
      if (esc == "u") {
        indx++;
        parse_char("{");
        String point = "";
        while (code[indx] != "}") {
          if ("0123456789abcdefABCDEF".contains(code[indx])) {
            point += code[indx++];
          } else {
            throw Exception(
              'Expected hexadecimal Unicode codepoint", found ' + code[indx] + ' at ' + indx.toString() + ".",
            );
          }
        }
        indx++;
        return String.fromCharCode(
          int.parse(point, radix: 16),
        );
      }
      if (esc == "\\") {
        indx++;
        return esc;
      }
      if (esc == '"') {
        indx++;
        return esc;
      }
      if (esc == "'") {
        indx++;
        return esc;
      }
      throw Exception(
        "Unexpected escape char: '\\" + code[indx + 1].toString() + "'.",
      );
    } else {
      return code[indx++];
    }
  }

  Term Function(Liist) parse_term() {
    parse_spaces();
    final String chr = code[indx++];
    switch (chr) {
      case "*":
        return (final a) => const _TermTypImpl();
      case "@":
      case "%":
        final eras = chr == "%";
        final self = parse_name();
        parse_char("(");
        final name = parse_name();
        parse_char(":");
        final bind = parse_term();
        parse_char(")");
        final body = parse_term();
        return (final ctx) => _TermAllImpl(
              eras: eras,
              self: self,
              name: name,
              bind: bind(ctx),
              body: (final s, final x) => body(
                _ext(
                  _CtxImpl(
                    name: name,
                    type: x,
                  ),
                  _ext(
                    _CtxImpl(name: self, type: s),
                    ctx,
                  ),
                ),
              ),
            );
      case "#":
        final name = parse_name();
        final body = parse_term();
        return (final ctx) => _TermLamImpl(
              name: name,
              body: (final x) => body(
                _ext(_CtxImpl(name: name, type: x), ctx),
              ),
            );
      case "(":
        final func = parse_term();
        final argm = parse_term();
        parse_char(")");
        return (final ctx) => _TermAppImpl(
              func: func(ctx),
              argm: argm(ctx),
            );
      case "!":
        final name = parse_name();
        parse_char("=");
        final expr = parse_term();
        parse_char(";");
        final body = parse_term();
        return (final ctx) => _TermLetImpl(
              name: name,
              expr: expr(ctx),
              body: (final x) => body(
                _ext(
                  _CtxImpl(name: name, type: x),
                  ctx,
                ),
              ),
            );
      case "\$":
        final name = parse_name();
        parse_char("=");
        final expr = parse_term();
        parse_char(";");
        final body = parse_term();
        return (final ctx) => _TermDefImpl(
              name: name,
              expr: expr(ctx),
              body: (final x) => body(
                _ext(
                  _CtxImpl(name: name, type: x),
                  ctx,
                ),
              ),
            );
      case "{":
        final expr = parse_term();
        parse_char(":");
        final type = parse_term();
        parse_char("}");
        return (final ctx) => _TermAnnImpl(
              done: false,
              expr: expr(ctx),
              type: type(ctx),
            );
      case "'":
        final chrx = parse_tokn();
        parse_char("'");
        return (ctx) => _TermChrImpl(chrx: chrx);
      case '"':
        var strx = "";
        while (code[indx] != '"') {
          // ignore: use_string_buffers
          strx += parse_tokn();
        }
        parse_char('"');
        return (final ctx) => _TermStrImpl(strx: strx);
      case '+':
        final numb = chr + parse_name();
        return (final ctx) => _TermNatImpl(natx: BigInt.parse(numb));
      default:
        if (is_name(chr)) {
          final name = chr + parse_name();
          final brui = () {
            if (code[indx] == "^") {
              indx++;
              return int.parse(parse_name());
            } else {
              return 0;
            }
          }();
          return (final ctx) => _list_find<Term>(
                ctx,
                (final x, final _indx) => x.name == name,
                0,
                brui,
                (final a, final _indx) => a.type,
                () => _TermRefImpl(
                  name: name,
                ),
              );
        } else {
          throw Exception("Unexpected symbol: '" + chr + "' at " + indx.toString() + ".");
        }
    }
  }

  void _parse_defs(
    final Map<String, Def> defs,
  ) {
    parse_spaces();
    final name = parse_name();
    if (name.isNotEmpty) {
      parse_char(":");
      final type = parse_term()(_nil());
      parse_char("=");
      final term = parse_term()(_nil());
      parse_char(";");
      defs.set(name, _DefImpl(type: type, term: term));
      _parse_defs(defs);
    }
  }
}

// Evaluation

Term _unroll_nat(
  final TermNat term,
) {
  if (term.natx == BigInt.zero) {
    return const _TermRefImpl(name: "Nat.zero");
  } else {
    return _TermAppImpl(
      func: const _TermRefImpl(name: "Nat.succ"),
      argm: _TermNatImpl(natx: term.natx - BigInt.one),
    );
  }
}

Term _unroll_chr(
  final TermChr term,
) {
  Term done = const _TermRefImpl(name: "Char.new");
  final ccod = term.chrx.codeUnitAt(0);
  for (int i = 0; i < 16; ++i) {
    done = _TermAppImpl(
      func: done,
      argm: _TermRefImpl(
        name: () {
          if ((ccod >>> (16 - i - 1)) & 1 == 1) {
            return "Bit.1";
          } else {
            return "Bit.0";
          }
        }(),
      ),
    );
  }
  return done;
}

Term _unroll_str(
  final TermStr term,
) {
  if (term.strx.isEmpty) {
    return const _TermRefImpl(name: "String.nil");
  } else {
    final chr = _unroll_chr(
      _TermChrImpl(
        chrx: term.strx[0],
      ),
    );
    return _TermAppImpl(
      func: _TermAppImpl(
        func: const _TermRefImpl(
          name: "String.cons",
        ),
        argm: chr,
      ),
      argm: _TermStrImpl(
        strx: term.strx.substring(1),
      ),
    );
  }
}

Term _reduce(
  final Term term,
  final Defs defs,
) =>
    term.match(
      vaar: (final a) => _TermVaarImpl(
        name: a.name,
        indx: a.indx,
      ),
      ref: (final a) {
        final got = defs.get(a.name);
        if (got != null) {
          return _reduce(got.term, defs);
        } else {
          return _TermRefImpl(name: a.name);
        }
      },
      typ: (final a) => const _TermTypImpl(),
      all: (final a) => _TermAllImpl(
        eras: a.eras,
        self: a.self,
        name: a.name,
        bind: a.bind,
        body: a.body,
      ),
      lam: (final a) => _TermLamImpl(
        name: a.name,
        body: a.body,
      ),
      app: (final a) => is_term_lam(
        _reduce(a.func, defs),
        (final func) => _reduce(func.body(a.argm), defs),
        (final func) => _TermAppImpl(func: func, argm: a.argm),
      ),
      let: (final a) => _reduce(a.body(a.expr), defs),
      def: (final a) => _reduce(a.body(a.expr), defs),
      ann: (final a) => _reduce(a.expr, defs),
      nat: (final a) => _reduce(_unroll_nat(a), defs),
      chr: (final a) => _reduce(_unroll_chr(a), defs),
      str: (final a) => _reduce(_unroll_str(a), defs),
    );

Term _normalize(
  final Term term,
  final Defs defs,
) {
  final norm = _reduce(term, defs);
  return norm.match(
    vaar: (final a) => _TermVaarImpl(
      name: a.name,
      indx: a.indx,
    ),
    ref: (final a) => _TermRefImpl(
      name: a.name,
    ),
    typ: (final a) => const _TermTypImpl(),
    all: (final a) => _TermAllImpl(
      eras: a.eras,
      self: a.self,
      name: a.name,
      bind: _normalize(a.bind, defs),
      body: (final s, final x) => _normalize(
        a.body(s, x),
        defs,
      ),
    ),
    lam: (final a) => _TermLamImpl(
      name: a.name,
      body: (final x) => _normalize(
        a.body(x),
        defs,
      ),
    ),
    app: (final a) => _TermAppImpl(
      func: _normalize(a.func, defs),
      argm: _normalize(a.argm, defs),
    ),
    let: (final a) => _normalize(
      a.body(a.expr),
      defs,
    ),
    def: (final a) => _normalize(
      a.body(a.expr),
      defs,
    ),
    ann: (final a) => _normalize(
      a.expr,
      defs,
    ),
    nat: (final a) => _TermNatImpl(
      natx: a.natx,
    ),
    chr: (final a) => _TermChrImpl(
      chrx: a.chrx,
    ),
    str: (final a) => _TermStrImpl(
      strx: a.strx,
    ),
  );
}

// Equality

/// Serializes a term to a string that identifies it uniquely.
String _serialize(
  final Term term,
  final int dep,
  final int ini,
) {
  return term.match(
    vaar: (final a) {
      final lvl = a.indx;
      if (lvl >= ini) {
        return "^-" + (dep - lvl - 1).toString();
      } else {
        return "^+" + lvl.toString();
      }
    },
    ref: (final a) => "\$" + a.name,
    typ: (final a) => "*",
    all: (final a) {
      final init = () {
        if (a.eras) {
          return "%";
        } else {
          return "@";
        }
      }();
      final self = a.self;
      final bind = _serialize(a.bind, dep, ini);
      final body = _serialize(
        a.body(
          _TermVaarImpl(name: "", indx: dep),
          _TermVaarImpl(name: "", indx: dep + 1),
        ),
        dep + 1,
        ini,
      );
      return init + self + bind + body;
    },
    lam: (final a) {
      final body = _serialize(a.body(_TermVaarImpl(name: "", indx: dep)), dep + 1, ini);
      return "#" + body;
    },
    app: (final a) {
      final func = _serialize(a.func, dep, ini);
      final argm = _serialize(a.argm, dep, ini);
      return "(" + func + " " + argm + ")";
    },
    let: (final a) {
      final expr = _serialize(a.expr, dep, ini);
      final body = _serialize(a.body(_TermVaarImpl(name: "", indx: dep)), dep + 1, ini);
      return "!" + expr + body;
    },
    def: (final a) {
      final expr = _serialize(a.expr, dep, ini);
      final body = _serialize(a.body(_TermVaarImpl(name: "", indx: dep)), dep + 1, ini);
      return "\$" + expr + body;
    },
    ann: (final a) => _serialize(a.expr, dep, ini),
    nat: (final a) => "+" + a.natx.toString(),
    chr: (final a) => "'" + a.chrx + "'",
    str: (final a) => '"' + a.strx + '"',
  );
}

/// Are two terms equal?
bool _equal(
  final Term a,
  final Term b,
  final Defs defs,
  final int dep,
  final Map<String, bool> seen,
) {
  final a1 = _reduce(a, defs);
  final b1 = _reduce(b, defs);
  final ah = _serialize(a1, dep, dep);
  final bh = _serialize(b1, dep, dep);
  final id = ah + "==" + bh;
  if (ah == bh || (seen.get(id) ?? false)) {
    return true;
  } else {
    seen.set(id, true);
    if (a1 is TermAll && b1 is TermAll) {
      final a1_body = a1.body(
        _TermVaarImpl(name: a1.self, indx: dep),
        _TermVaarImpl(name: a1.name, indx: dep + 1),
      );
      final b1_body = b1.body(
        _TermVaarImpl(name: a1.self, indx: dep),
        _TermVaarImpl(name: a1.name, indx: dep + 1),
      );
      return a1.eras == b1.eras &&
          a1.self == b1.self &&
          _equal(a1.bind, b1.bind, defs, dep, seen) &&
          _equal(a1_body, b1_body, defs, dep + 2, seen);
    }
    if (a1 is TermLam && b1 is TermLam) {
      final a1_body = a1.body(_TermVaarImpl(name: a1.name, indx: dep));
      final b1_body = b1.body(_TermVaarImpl(name: a1.name, indx: dep));
      return _equal(a1_body, b1_body, defs, dep + 1, seen);
    }
    if (a1 is TermApp && b1 is TermApp) {
      return _equal(a1.func, b1.func, defs, dep, seen) && _equal(a1.argm, b1.argm, defs, dep, seen);
    }
    if (a1 is TermLet && b1 is TermLet) {
      final a1_body = a1.body(_TermVaarImpl(name: a1.name, indx: dep));
      final b1_body = b1.body(_TermVaarImpl(name: a1.name, indx: dep));
      return _equal(a1.expr, b1.expr, defs, dep, seen) && _equal(a1_body, b1_body, defs, dep + 1, seen);
    }
    if (a1 is TermAnn && b1 is TermAnn) {
      return _equal(a1.expr, b1.expr, defs, dep, seen);
    }
    return false;
  }
}

// Type-Checking

Term _typeinfer(
  final Term term,
  final Defs defs,
  final Liist ctx,
) =>
    term.match(
      vaar: (final a) => _TermVaarImpl(name: a.name, indx: a.indx),
      ref: (final a) {
        final got = defs.get(a.name);
        if (got != null) {
          return got.type;
        } else {
          _error(term, ctx, "Unbound reference: '" + a.name + "'.");
        }
      },
      typ: (final a) => const _TermTypImpl(),
      app: (final a) {
        final func_typ = _reduce(_typeinfer(a.func, defs, ctx), defs);
        return is_term_all(
          func_typ,
          (final func_typ) {
            final self_var = _TermAnnImpl(done: true, expr: a.func, type: func_typ);
            final name_var = _TermAnnImpl(done: true, expr: a.argm, type: func_typ.bind);
            _typecheck(a.argm, func_typ.bind, defs, ctx);
            final term_typ = func_typ.body(self_var, name_var);
            return term_typ;
          },
          () {
            _error(term, ctx, "Non-function application.");
          },
        );
      },
      let: (final a) {
        final expr_typ = _typeinfer(a.expr, defs, ctx);
        final expr_var = _TermAnnImpl(
          done: true,
          expr: _TermVaarImpl(name: a.name, indx: ctx.size + 1),
          type: expr_typ,
        );
        final body_ctx = _ext(_CtxImpl(name: a.name, type: expr_var.type), ctx);
        final body_typ = _typeinfer(a.body(expr_var), defs, body_ctx);
        return body_typ;
      },
      def: (final a) => _typeinfer(a.body(a.expr), defs, ctx),
      all: (final a) {
        final self_var = _TermAnnImpl(
          done: true,
          expr: _TermVaarImpl(name: a.self, indx: ctx.size),
          type: a,
        );
        final name_var = _TermAnnImpl(
          done: true,
          expr: _TermVaarImpl(name: a.name, indx: ctx.size + 1),
          type: a.bind,
        );
        final _body_ctx = _ext(_CtxImpl(name: a.self, type: self_var.type), ctx);
        final body_ctx = _ext(_CtxImpl(name: a.name, type: name_var.type), _body_ctx);
        _typecheck(a.bind, const _TermTypImpl(), defs, ctx);
        _typecheck(a.body(self_var, name_var), const _TermTypImpl(), defs, body_ctx);
        return const _TermTypImpl();
      },
      ann: (final a) {
        if (!a.done) {
          _typecheck(a.expr, a.type, defs, ctx);
          return a.type;
        } else {
          // There's no need to typecheck.
          return a.type;
        }
      },
      nat: (final a) => const _TermRefImpl(name: "Nat"),
      chr: (final a) => const _TermRefImpl(name: "Char"),
      str: (final a) => const _TermRefImpl(name: "String"),
      lam: (final a) => _error(a, ctx, "Can't infer"),
    );

void _typecheck(
  final Term term,
  final Term type,
  final Defs defs,
  final Liist ctx,
) {
  final typv = _reduce(type, defs);
  void _default() {
    final infr = _typeinfer(term, defs, ctx);
    final eq = _equal(type, infr, defs, ctx.size, {});
    if (eq) {
      // Type checks.
    } else {
      // FormCoreJs passes ctx to show which has an incompatible type.
      final type0_str = _show(_normalize(type, {}), 0);
      // FormCoreJs passes ctx to show which has an incompatible type.
      final infr0_str = _show(_normalize(infr, {}), 0);
      _error(
        term,
        ctx,
        "Found type: \x1b[2m" + infr0_str + "\x1b[0m\n" + "Instead of: \x1b[2m" + type0_str + "\x1b[0m",
      );
    }
  }

  term.match(
    lam: (final a) => is_term_all(
      typv,
      (final typv) {
        final self_var = _TermAnnImpl(
          done: true,
          expr: a,
          type: type,
        );
        final name_var = _TermAnnImpl(
          done: true,
          expr: _TermVaarImpl(name: a.name, indx: ctx.size + 1),
          type: typv.bind,
        );
        final body_typ = typv.body(self_var, name_var);
        final body_ctx = _ext(_CtxImpl(name: a.name, type: name_var.type), ctx);
        _typecheck(a.body(name_var), body_typ, defs, body_ctx);
      },
      () => _error(
        term,
        ctx,
        "Lambda has a non-function type.",
      ),
    ),
    let: (final a) {
      final expr_typ = _typeinfer(a.expr, defs, ctx);
      final expr_var = _TermAnnImpl(
        done: true,
        expr: _TermVaarImpl(name: a.name, indx: ctx.size + 1),
        type: expr_typ,
      );
      final body_ctx = _ext(_CtxImpl(name: a.name, type: expr_var.type), ctx);
      _typecheck(a.body(expr_var), type, defs, body_ctx);
    },
    vaar: (final a) => _default(),
    ref: (final a) => _default(),
    typ: (final a) => _default(),
    all: (final a) => _default(),
    app: (final a) => _default(),
    def: (final a) => _default(),
    ann: (final a) => _default(),
    nat: (final a) => _default(),
    chr: (final a) => _default(),
    str: (final a) => _default(),
  );
}

// Model helpers

Never _error(
  final Term term,
  final Liist ctx,
  final String msg,
) =>
    throw _ErrImpl(
      term: term,
      ctx: ctx,
      msg: msg,
    );

LiistNil _nil() => const _LiistNilImpl(
      size: 0,
    );

LiistExt _ext(
  final Ctx head,
  final Liist tail,
) =>
    _LiistExtImpl(
      head: head,
      tail: tail,
      size: tail.size + 1,
    );

// Model implementations.

class _ErrImpl implements Err {
  @override
  final Term term;

  @override
  final Liist ctx;

  @override
  final String msg;

  const _ErrImpl({
    required final this.term,
    required final this.ctx,
    required final this.msg,
  });
}

class _TermVaarImpl implements TermVaar {
  @override
  final String name;

  @override
  final int indx;

  const _TermVaarImpl({
    required final this.name,
    required final this.indx,
  });
}

class _TermRefImpl implements TermRef {
  @override
  final String name;

  const _TermRefImpl({
    required final this.name,
  });
}

class _TermTypImpl implements TermTyp {
  const _TermTypImpl();
}

class _TermAllImpl implements TermAll {
  @override
  final bool eras;

  @override
  final String self;

  @override
  final String name;

  @override
  final Term bind;

  @override
  final Term Function(Term self_var, Term name_var) body;

  const _TermAllImpl({
    required final this.eras,
    required final this.self,
    required final this.name,
    required final this.bind,
    required final this.body,
  });
}

class _TermLamImpl implements TermLam {
  @override
  final String name;

  @override
  final Term Function(Term name_var) body;

  const _TermLamImpl({
    required final this.name,
    required final this.body,
  });
}

class _TermAppImpl implements TermApp {
  @override
  final Term func;

  @override
  final Term argm;

  const _TermAppImpl({
    required final this.func,
    required final this.argm,
  });
}

class _TermLetImpl implements TermLet {
  @override
  final String name;

  @override
  final Term expr;

  @override
  final Term Function(Term) body;

  const _TermLetImpl({
    required final this.name,
    required final this.expr,
    required final this.body,
  });
}

class _TermDefImpl implements TermDef {
  @override
  final String name;

  @override
  final Term expr;

  @override
  final Term Function(Term) body;

  const _TermDefImpl({
    required final this.name,
    required final this.expr,
    required final this.body,
  });
}

class _TermAnnImpl implements TermAnn {
  @override
  final bool done;

  @override
  final Term expr;

  @override
  final Term type;

  const _TermAnnImpl({
    required final this.done,
    required final this.expr,
    required final this.type,
  });
}

class _TermNatImpl implements TermNat {
  @override
  final BigInt natx;

  const _TermNatImpl({
    required final this.natx,
  });
}

class _TermChrImpl implements TermChr {
  @override
  final String chrx;

  const _TermChrImpl({
    required final this.chrx,
  });
}

class _TermStrImpl implements TermStr {
  @override
  final String strx;

  const _TermStrImpl({
    required final this.strx,
  });
}

class _LiistNilImpl implements LiistNil {
  @override
  final int size;

  const _LiistNilImpl({
    required final this.size,
  });
}

class _LiistExtImpl implements LiistExt {
  @override
  final Ctx head;

  @override
  final Liist tail;

  @override
  final int size;

  const _LiistExtImpl({
    required final this.head,
    required final this.tail,
    required final this.size,
  });
}

class _DefImpl implements Def {
  @override
  final Term type;

  @override
  final Term term;

  const _DefImpl({
    required final this.type,
    required final this.term,
  });
}

class _CtxImpl implements Ctx {
  @override
  final String name;

  @override
  final Term type;

  const _CtxImpl({
    required final this.name,
    required final this.type,
  });
}

R is_term_all<R>(
  final Term term,
  final R Function(TermAll) termAll,
  final R Function() otherwise,
) {
  if (term is TermAll) {
    return termAll(term);
  } else {
    return otherwise();
  }
}

R is_term_lam<R>(
  final Term term,
  final R Function(TermLam) termLam,
  final R Function(Term) otherwise,
) {
  if (term is TermLam) {
    return termLam(term);
  } else {
    return otherwise(term);
  }
}

extension<K, V> on Map<K, V> {
  V? get(
    final K k,
  ) =>
      this[k];

  void set(
    final K k,
    final V v,
  ) =>
      this[k] = v;
}
