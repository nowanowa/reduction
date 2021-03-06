# reduction

- 与えられた素因数分解問題をSATもしくはQUBOに帰着します
- SATはminisatに解かせます。その際にtemp.dimacsを出力します
- QUBOはwildqatに解かせます
- 帰着先（minisatやwildqat）の回答の因数が8bit以上になると、回答を整数にdecodeできません
  - 取り急ぎ8bit以下用として作っていたためです
  - encodeだけならできることに気付いたので入力サイズチェックをコメントアウトしました


SAT

    >>> import facrtorize
    >>> s = factorize.sat(143)   # 143を素因数分解
    >>> s.setbitlen(4,4)         # 4bit×4bit以下の回答を探します
    >>> s.setcnfsat()            # s.clausesに節が格納されます　変数の数はs.varsize
    >>> s.run_sat()              # minisatを呼んで走らせます
    >>> s.satisfiability
    'SAT'
    >>> s.facts
    array([13, 11], dtype=uint8)

QUBO

    >>> import facrtorize
    >>> q = facrtorize.annealer(143)      # 143を素因数分解
    >>> q.setbitlen(4,4)         # 4bit×4bit以下の回答を探します
    >>> q.setqubo()              # s.quboにQUBOmatrixが格納されます
    >>> q.run_sqa()              # wildqatのSQAを走らせます　q.rum_qa()もあります
    array([[0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
           [0, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0],
           [1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
           [0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
           [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
           [0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0],
           [1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0],
           [1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0]])
    >>> q.factss                 # 今回は見つかりませんでした
    array([[ 5,  3],
           [ 9,  7],
           [ 3,  3],
           [ 5,  3],
           [15, 15],
           [ 9, 11],
           [11,  3],
           [15, 11]], dtype=uint8)
    >>> q.Hs                     # ハミルトニアンが-(143-1)**2=-20164になれば目的の解ですがなりませんでした
    array([ -3780., -13764.,  -2208.,  -3780., -13440., -18228.,  -8064.,
           -19680.])
