<TeXmacs|1.99.2>

<style|<tuple|generic|german>>

<\body>
  <doc-data|<doc-title|Von-Neumann-Dimension>|<doc-author|<author-data|<author-name|Tim
  Baumann>>>>

  Wir wollen einen Dimensionsbegriff für Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln
  definieren. Bei endlich-dimensionalen Vektorräumen gilt: Die Dimension
  eines Vektorraums <math|V> ist die Spur der Identitätsabbildung auf
  <math|V>. Diese Gleichheit wollen wir als Definition der Dimension von
  Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln verwenden. Dazu müssen wir
  definieren, was die Spur eines Morphismus zwischen
  Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln ist.

  <with|color|dark magenta|TODO: Normierungs-Eigenschaft>

  Erinnerung: Die Spur von <math|f\<in\>\<cal-N\><around*|(|G|)>> ist
  definiert als <math|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>\<assign\><around*|\<langle\>|f<around*|(|e|)>,e|\<rangle\>>>.
  Wir benötigen ein paar Lemmata zur Spur:

  <\definition*>
    Die <strong|Konjugationsabbildung> auf <math|l<rsup|2><around*|(|G|)>>
    ist definiert durch

    <\equation*>
      <wide|<space|0.8em>|\<bar\>> : l<rsup|2><around*|(|G|)>\<rightarrow\>l<rsup|2><around*|(|G|)>,<space|1em><big|sum><rsub|g\<in\>G>\<lambda\><rsub|g>\<cdot\>g<rsub|>\<mapsto\><big|sum><rsub|g\<in\>G>\<lambda\><rsub|g>\<cdot\>g<rsup|-1>.
    </equation*>
  </definition*>

  <\lemma*>
    Für <math|b\<in\>H>, <math|f\<in\>\<cal-N\><around*|(|G|)>> gilt
    <math|f<rsup|\<ast\>><around*|(|e|)>=<overline|f<around*|(|e|)>>>.
  </lemma*>

  <\proof>
    Für ein beliebiges <math|g\<in\>G>, gilt

    <\eqnarray*>
      <tformat|<cwith|2|2|2|2|cell-halign|l>|<cwith|1|1|2|2|cell-halign|l>|<cwith|3|3|2|2|cell-halign|l>|<table|<row|<cell|<around*|\<langle\>|f<rsup|\<ast\>><around*|(|e|)>,g|\<rangle\>>>|<cell|=
      <around*|\<langle\>|e,f<around*|(|g|)>|\<rangle\>>>|<cell|=
      <around*|\<langle\>|e,g.f<around*|(|e|)>|\<rangle\>>>>|<row|<cell|>|<cell|=
      <around*|\<langle\>|g<rsup|-1>,f<around*|(|e|)>|\<rangle\>>>|<cell|=
      <around*|\<langle\>|<overline|g>,f<around*|(|e|)>|\<rangle\>>>>|<row|<cell|>|<cell|=
      <around*|\<langle\>|g,<overline|f<around*|(|e|)>>|\<rangle\>>>|<cell|=
      <around*|\<langle\>|<overline|f<around*|(|e|)>>,g|\<rangle\>>.>>>>
    </eqnarray*>
  </proof>

  Wir wollen zunächst diese Definition verallgemeinern auf Morphismen
  zwischen Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln. Das wird uns
  gelingen für folgende Klasse von Morphismen:

  <\definition*>
    Sei <math|H> ein Hilbertraum. Ein Operator
    <math|f\<in\>\<cal-B\><around*|(|H|)>> heiÿt <strong|positiv>, falls
    <math|<around*|\<langle\>|f<around*|(|v|)>,v|\<rangle\>>\<in\>\<bbb-R\><rsub|\<geqslant\>0>>
    für alle <math|v\<in\>H>.
  </definition*>

  <\lemma*>
    Es gilt: <math|f> ist positiv \ \ <math|\<Longleftrightarrow\>>
    \ \ <math|\<exists\> g\<in\>\<cal-B\><around*|(|H|)> : f =
    g<rsup|<math-up|*>>g>
  </lemma*>

  <\corollary*>
    Positive Operatoren sind selbstadjungiert.
  </corollary*>

  <\theorem*>
    Für alle positiven <math|f\<in\>\<cal-B\><around*|(|H|)>> gibt es genau
    eine positive Quadratwurzel, d.h. ein
    <math|f<rsup|<frac*|1|2>>\<in\>\<cal-B\><around*|(|H|)>> mit <math|f =
    f<rsup|<frac*|1|2>> \<circ\> f<rsup|<frac*|1|2>>>.
  </theorem*>

  <strong|Beweis>: siehe [R], Thm 12.32

  <\notation*>
    <math|f<rsub|1>\<leqslant\>f<rsub|2><space|1em>:\<Longleftrightarrow\><space|1em><around*|(|f<rsub|2>-f<rsub|1>|)>>
    ist positiv
  </notation*>

  <\lemma*>
    Sei <math|V> ein Hilbertraum mit unitärer <math|G>-Wirkung, <math|W
    \<subset\> V> ein abgeschlossener Unterraum, der unter der
    <math|G>-Wirkung abgeschlossen ist. Dann ist die orthogonale Projektion
    <math|pr<rsub|W> : V \<rightarrow\> W> auf <math|W> <math|G>-äquivariant.
  </lemma*>

  <\proof>
    Sei <math|g \<in\> G>, <math|x \<in\> V>. Schreibe <math|x =
    x<rsub|<big|parallel>>+x<rsub|\<perp\>>> mit
    <math|x<rsub|<big|parallel>>\<in\>W> und
    <math|x<rsub|\<perp\>>\<in\>W<rsup|\<perp\>>>. Es gilt
    <math|g.x<rsub|\<perp\>>\<in\>W<rsup|\<perp\>>>, da

    <\equation*>
      \<forall\>w\<in\>W:<around*|\<langle\>|g.x<rsub|\<perp\>>,w|\<rangle\>>
      = <around*|\<langle\>|x<rsub|\<perp\>>,g<rsup|-1>.w|\<rangle\>> = 0.
    </equation*>

    Somit gilt

    <\equation*>
      pr<rsub|W><around*|(|g.x|)>=pr<rsub|W><around*|(|g.x<rsub|<big|parallel>>|)>+pr<rsub|W><around*|(|g.x<rsub|\<perp\>>|)>=pr<rsub|W><around*|(|g.x<rsub|<big|parallel>>|)>+0=g.x<rsub|<big|parallel>>
      = g.pr<rsub|W><around*|(|x|)>.
    </equation*>
  </proof>

  <\definition*>
    <dueto|[L], 1.8>Sei <math|V> ein Hilbert-<math|\<cal-N\><around*|(|G|)>>-Modul,
    <math|f\<in\>\<cal-B\><around*|(|H|)>> positiv. Wähle einen Hilbertraum
    <math|H>, eine isometrische <math|G>-äquivariante, lineare Einbettung
    <math|i : V \<rightarrow\> H\<otimes\>l<rsup|2><around*|(|G|)>> und eine
    Hilbertbasis <math|<around*|(|b<rsub|i>|)><rsub|i\<in\>I>> von <math|H>.
    Sei <math|pr<rsub|im<around*|(|i|)>> :
    H\<otimes\>l<rsup|2><around*|(|G|)>\<rightarrow\>im<around*|(|i|)>> die
    orthogonale Projektion auf <math|im<around*|(|i|)>>. Sei
    <math|<overline|f>> die Komposition

    <\equation*>
      H\<otimes\>l<rsup|2><around*|(|G|)><long-arrow|\<rubber-rightarrow\>|pr<rsub|im<around*|(|i|)>>>im<around*|(|i|)><long-arrow|\<rubber-rightarrow\>|i<rsup|-1>>V<long-arrow|\<rubber-rightarrow\>|f>V<long-arrow|\<rubber-rightarrow\>|i>im<around*|(|i|)>\<hookrightarrow\>H\<otimes\>l<rsup|2><around*|(|G|)>.
    </equation*>

    Die <strong|Von-Neumann-Spur> von <math|f> ist dann

    <\equation*>
      tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>\<assign\>
      <big|sum><rsub|i\<in\>I><around*|\<langle\>|<overline|f><around*|(|b<rsub|i>\<otimes\>e|)>,b<rsub|i>\<otimes\>e|\<rangle\>><space|1em>\<in\>
      <around*|[|0,\<infty\>|]>.
    </equation*>

    <\eqnarray*>
      <tformat|<cwith|2|2|2|2|cell-halign|r>|<table|<row|<cell|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>>|<cell|\<assign\>>|<cell|<big|sum><rsub|i\<in\>I><around*|\<langle\>|<overline|f><around*|(|b<rsub|i>\<otimes\>e|)>,b<rsub|i>\<otimes\>e|\<rangle\>><space|1em>\<in\>
      <around*|[|0,\<infty\>|]>.>>|<row|<cell|>|<cell|=>|<cell|<big|sum><rsub|i\<in\>I>tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|l<rsup|2><around*|(|G|)>\<cong\><around*|{|b<rsub|i>|}>\<otimes\>l<rsup|2><around*|(|G|)>\<hookrightarrow\>H\<otimes\>l<rsup|2><around*|(|G|)><long-arrow|\<rubber-rightarrow\>|<overline|f>>H\<otimes\>l<rsup|2><around*|(|G|)><long-arrow|\<rubber-rightarrow\>|pr><around*|{|b<rsub|i>|}>\<otimes\>l<rsup|2><around*|(|G|)>\<cong\>l<rsup|2><around*|(|G|)>|)>>>>>
    </eqnarray*>
  </definition*>

  <\remark*>
    Wenn <math|I> nicht abzählbar ist, dann wird die Summation folgendermaÿen
    interpretiert: Die Summe ist der Grenzwert des Netzes aller endlichen
    Teilsummen.
  </remark*>

  <\remark*>
    Wegen der Positivität von <math|f> sind alle Summanden in der Definition
    der Spur positiv. Es kommt daher nicht auf die Summationsreihenfolge an.
    Für positive <math|f\<in\>\<cal-N\><around*|(|G|)>> stimmen beide bisher
    gegebenen Definitionen von <math|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>>
    überein.
  </remark*>

  <\remark*>
    Wenn <math|V> endlich erzeugt ist, so ist
    <math|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)> \<less\>
    \<infty\>> für alle positiven <math|f : V \<rightarrow\> V>.
  </remark*>

  <\lemma*>
    Angenommen, <math|H> ist ein Hilbertraum mit unitärer <math|G>-Wirkung,
    <math|f \<in\> \<cal-B\><around*|(|H|)>> ein positiver, G-äquivarianter
    Operator. Dann ist die eindeutige positive Wurzel
    <math|f<rsup|<frac*|1|2>> \<in\> \<cal-B\><around*|(|H|)>> von <math|f>
    (d.h. <math|f = f<rsup|<frac*|1|2>> \<circ\> f<rsup|<frac*|1|2>>>)
    ebenfalls G-äquivariant.
  </lemma*>

  <\proof>
    Sei <math|g \<in\> G>. Zu zeigen: Für alle <math|x \<in\> H> gilt
    <math|f<rsup|<frac*|1|2>><around*|(|g.x|)> =
    g.f<rsup|<frac*|1|2>><around*|(|x|)> \<Leftrightarrow\>
    g<rsup|-1>.f<rsup|<frac*|1|2>><around*|(|g.x|)> =
    f<rsup|<frac*|1|2>><around*|(|x|)>>. Betrachte <math|h \<in\>
    \<cal-B\><around*|(|H|)>> definiert durch <math|h<around*|(|x|)>
    \<assign\> g<rsup|-1>.f<rsup|<frac*|1|2>><around*|(|g.x|)>>. Es gilt
    <math|h\<circ\>h<around*|(|x|)> = g<rsup|-1>.f<around*|(|g.x|)> =
    f<around*|(|x|)>>, also ist <math|h> eine Quadratwurzel von <math|f>.
    Auÿerdem ist <math|h> positiv:

    <\equation*>
      <around*|\<langle\>|h<around*|(|x|)>,x|\<rangle\>>=<around*|\<langle\>|g<rsup|-1>.f<rsup|<frac*|1|2>><around*|(|g.x|)>,x|\<rangle\>>=<around*|\<langle\>|f<rsup|<frac*|1|2>><around*|(|g.x|)>,g.x|\<rangle\>>
      \<geqslant\> 0,
    </equation*>

    wobei die zweite Gleichheit gilt, da <math|y \<mapsto\> g<rsup|-1>.y>
    unitär mit Adjungierten/Inversen <math|y \<mapsto\> g.y> ist. Aus der
    Eindeutigkeit der positiven Quadratwurzel von <math|f> folgt
    <math|f<rsup|<frac*|1|2>> = h>.
  </proof>

  <\lemma*>
    Die Definition der Von-Neumann-Spur ist unabhängig von der Wahl der
    Basis.
  </lemma*>

  <\proof>
    Sei <math|<around*|(|c<rsub|j>|)><rsub|j\<in\>J>> eine weitere Basis von
    <math|H>. Dann ist

    <\eqnarray*>
      <tformat|<cwith|1|1|2|2|cell-halign|l>|<cwith|3|3|2|2|cell-halign|l>|<cwith|4|4|2|2|cell-halign|l>|<cwith|5|5|2|2|cell-halign|l>|<cwith|6|6|2|2|cell-halign|l>|<cwith|2|2|2|2|cell-halign|l>|<table|<row|<cell|<big|sum><rsub|i\<in\>I><around*|\<langle\>|<overline|f><around*|(|b<rsub|i>\<otimes\>e|)>,b<rsub|i>\<otimes\>e|\<rangle\>>>|<cell|=
      <big|sum><rsub|i\<in\>I><around*|\<\|\|\>|<overline|f>
      <rsup|<frac*|1|2>><around*|(|b<rsub|i>\<otimes\>e|)>|\<\|\|\>><rsup|2>>|<cell|>>|<row|<cell|>|<cell|=
      <big|sum><rsub|i\<in\>I><big|sum><rsub|j\<in\>J><big|sum><rsub|g\<in\>G><around*|\||<around*|\<langle\>|<overline|f>
      <rsup|<frac*|1|2>><around*|(|b<rsub|i>\<otimes\>e|)>,c<rsub|j>\<otimes\>g|\<rangle\>>|\|><rsup|2>>|<cell|>>|<row|<cell|>|<cell|=
      <big|sum><rsub|i\<in\>I><big|sum><rsub|j\<in\>J><big|sum><rsub|g\<in\>G><around*|\||<around*|\<langle\>|b<rsub|i>\<otimes\>e,<overline|f>
      <rsup|<frac*|1|2>><around*|(|c<rsub|j>\<otimes\>g|)>|\<rangle\>>|\|><rsup|2>>|<cell|>>|<row|<cell|>|<cell|=
      <big|sum><rsub|j\<in\>J><big|sum><rsub|i\<in\>I><big|sum><rsub|g\<in\>G><around*|\||<around*|\<langle\>|b<rsub|i>\<otimes\>g<rsup|-1>,<overline|f>
      <rsup|<frac*|1|2>><around*|(|c<rsub|j>\<otimes\>e|)>|\<rangle\>>|\|><rsup|2>>|<cell|>>|<row|<cell|>|<cell|=
      <big|sum><rsub|j\<in\>J><around*|\<\|\|\>|<overline|f>
      <rsup|<frac*|1|2>><around*|(|c<rsub|j>\<otimes\>e|)>|\<\|\|\>><rsup|2>>|<cell|>>|<row|<cell|>|<cell|=
      <big|sum><rsub|j\<in\>J><around*|\<langle\>|<overline|f><around*|(|c<rsub|j>\<otimes\>e|)>,c<rsub|j>\<otimes\>e|\<rangle\>>>|<cell|>>>>
    </eqnarray*>

    Hierbei haben wir verwendet: Die Parseval-Identität, die Tatsache, dass
    <math|G> isometrisch wirkt und die <math|G>-Äquivarianz von
    <math|<overline|f> <rsup|<frac*|1|2>>> (siehe vorheriges Lemma).
  </proof>

  \;

  <\lemma*>
    Die Definition der Von-Neumann-Spur ist unabhängig von der Wahl der
    isometrischen, <math|G>-äquivarianten Einbettung
    <math|V\<hookrightarrow\>H\<otimes\>l<rsup|2><around*|(|G|)>>.
  </lemma*>

  <\proof>
    Seien <math|H<rsub|1>>, <math|H<rsub|2>> zwei Hilberträume und
    <math|i<rsub|1/2> : V\<hookrightarrow\>H<rsub|1/2>\<otimes\>l<rsup|2><around*|(|G|)>>
    zwei <math|G>-äquivariante isometrische Einbettungen. Betrachte die
    beiden Einbettungen

    <\equation*>
      <wide|i|~><rsub|1/2> := <around*|(|V<long-arrow|\<rubber-rightarrow\>|i<rsub|1/2>>H<rsub|1/2>\<otimes\>l<rsup|2><around*|(|G|)>\<hookrightarrow\><around*|(|H<rsub|1>\<oplus\>H<rsub|2>|)>\<otimes\>l<rsup|2><around*|(|G|)>|)>.
    </equation*>

    Man sieht leicht: Die Einbettungen <math|i<rsub|1>> und
    <math|<wide|i|~><rsub|1>> liefern in der Definition der Von-Neumann-Spur
    dasselbe Ergebnis. Gleiches gilt für <math|i<rsub|2>> und
    <math|<wide|i|~><rsub|2>>. Wir dürfen somit ohne Einschränkung annehmen,
    dass <math|H<rsub|1>=H<rsub|2>=: H>.

    <with|color|dark magenta|TODO: Zeige Unabhängigkeit von Einbettung>
  </proof>

  <\lemma*>
    Sei <math|f\<in\>\<cal-B\><around*|(|V|)>> positiv, <math|u :
    W\<rightarrow\> V> unitär. Dann gilt <math|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>=tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|u<rsup|-1>
    f u|)>>.
  </lemma*>

  <\proof>
    Die Aussage folgt aus der Unabhängigkeit der Definition der Spur von der
    Wahl der isometrischen Einbettung <math|i : V \<rightarrow\>
    H\<otimes\>l<rsup|2><around*|(|G|)>>.
  </proof>

  <\definition*>
    Eine beschränkte, lineare Abbildung <math|u : V\<rightarrow\>W> zwischen
    Hilberträumen heiÿt <strong|partielle Isometrie>, wenn
    <math|u\|<rsub|ker<around*|(|u|)><rsup|\<perp\>>>> eine Isometrie (d.h.
    skalarprodukterhaltend) ist.
  </definition*>

  <\theorem*>
    <dueto|Polarzerlegung>Für alle beschränkten, linearen Abb. <math|f : V
    \<rightarrow\> W> zwischen Hilberträumen gibt es eine partielle Isometrie
    <math|u : V \<rightarrow\> W>, sodass <math|f=u <around*|\||f|\|>> mit
    <math|<around*|\||f|\|>\<assign\><around*|(|f<rsup|\<ast\>>
    f|)><rsup|<frac*|1|2>>>.
  </theorem*>

  <strong|Beweis>: siehe <with|color|dark magenta|TODO>

  <\lemma*>
    Jede kurze exakte Sequenz <math|0 \<rightarrow\> U
    <long-arrow|\<rubber-rightarrow\>|f> V
    <long-arrow|\<rubber-rightarrow\>|h> W \<rightarrow\> 0> von
    Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln spaltet und der
    Isomorphismus <math|V\<cong\>U\<oplus\>W> ist unitär.
  </lemma*>

  <\proof>
    <with|color|dark magenta|TODO>
  </proof>

  <\lemma*>
    Jede kurze schwach exakte Sequenz <math|0\<rightarrow\>U\<rightarrow\>V\<rightarrow\>W\<rightarrow\>0>
    von Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln lässt sich zu einer
    exakten Sequenz derselben Moduln verbessern.
  </lemma*>

  <\proof>
    Wir haben eine injektive, lineare, beschränkte, G-äquivariante Abbildung
    <math|f : U \<rightarrow\> ker<around*|(|h|)>> mit dichtem Bild. Nach
    [E], Lemma 2.5.3 gibt es eine <math|G>-äquivariante Isometrie
    <math|<wide|f|~>: U\<rightarrow\>ker<around*|(|h|)>>. Nun ist
    <math|h\|<rsub|ker<around*|(|h|)><rsup|\<perp\>>>> injektiv,<math|> das
    Bild <math|im<around*|(|h\|<rsub|ker<around*|(|g|)><rsup|\<perp\>>>|)> =
    im<around*|(|h|)>> liegt dicht in <math|W>, und
    <math|h\|<rsub|ker<around*|(|h|)><rsup|\<perp\>>>> ist
    <math|G>-äquivariant, da <math|ker<around*|(|h|)><rsup|\<perp\>>> unter
    der <math|G>-Wirkung abgeschlossen ist:

    <\equation*>
      \<forall\>v\<in\>ker<around*|(|h|)><rsup|\<perp\>>: \<forall\>g\<in\>G:
      \<forall\>w\<in\>ker<around*|(|h|)>:
      <around*|\<langle\>|g.v,w|\<rangle\>>=<around*|\<langle\>|v,g<rsup|-1>.w|\<rangle\>>=0,
    </equation*>

    da <math|f<around*|(|g<rsup|-1>.w|)>=g<rsup|-1>.f<around*|(|w|)>=g<rsup|-1>.0=0>,
    also <math|g<rsup|-1>.w\<in\>ker<around*|(|h|)>>. Somit gibt es (wieder
    nach [E], Lemma 2.5.3) eine <math|G>-äquivariante Isometrie
    <math|<wide|h|~> : ker<around*|(|h|)><rsup|\<perp\>>\<rightarrow\>W>. Wir
    haben also die kurze exakte Sequenz

    <\equation*>
      0\<rightarrow\>U<long-arrow|\<rubber-rightarrow\>|u\<mapsto\><around*|(|<wide|f|~><around*|(|u|)>,0|)>>ker<around*|(|h|)>\<oplus\>ker<around*|(|h|)><rsup|\<perp\>>\<cong\>V<long-arrow|\<rubber-rightarrow\>|<around*|(|x,y|)>\<mapsto\><wide|h|~><around*|(|y|)>>W\<rightarrow\>0.
    </equation*>
  </proof>

  <\theorem*>
    <dueto|[L], 1.9>Seien <math|U>, <math|V>, <math|W>
    Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln.
  </theorem*>

  <strong|1)> <strong|Monotonie>: Für positive Endomorphismen <math|f,g : V
  \<rightarrow\> V> mit <math|f \<leqslant\> g> gilt
  <math|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>\<leqslant\>tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|g|)>>.

  <\proof>
    <math|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>\<leqslant\>
    tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>+tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|g-f|)>=tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|g|)>>
  </proof>

  <strong|3) Positive Definitheit>: Für einen pos. Endomorphismus <math|f : V
  \<rightarrow\> V> gilt <math|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>=0>
  <math|\<Longleftrightarrow\>> \ <math|f=0>.

  <\proof>
    \R<math|\<Longrightarrow\>>`` \ Dann ist

    <\equation*>
      0 = tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>=<big|sum><rsub|i\<in\>I><around*|\<langle\>|<overline|f><around*|(|b<rsub|i>\<otimes\>e|)>,b<rsub|i>\<otimes\>e|\<rangle\>>=<big|sum><rsub|i\<in\>I><around*|\<\|\|\>|<overline|f>
      <rsup|<frac*|1|2>><around*|(|b<rsub|i>\<otimes\>e|)>|\<\|\|\>><rsup|2>.
    </equation*>

    Also ist <math|<overline|f> <rsup|<frac*|1|2>><around*|(|b<rsub|i>\<otimes\>e|)>=0>
    für alle <math|i \<in\>I>. Aus der <math|G>-Äquivarianz von
    <math|<overline|f> <rsup|<frac*|1|2>>> folgt <math|<overline|f>
    <rsup|<frac*|1|2>><around*|(|b<rsub|i>\<otimes\>g|)>=g.<overline|f>
    <rsup|<frac*|1|2>><around*|(|b<rsub|i>\<otimes\>e|)>=g.0=0> für alle
    <math|i\<in\>I> und <math|g\<in\>G>. Somit ist <math|<overline|f>
    <rsup|<frac*|1|2>> = 0>. Es folgt <math|<overline|f>=<overline|f>
    <rsup|<frac*|1|2>> \<circ\> <overline|f> <rsup|<frac*|1|2>> = 0> und
    schlieÿlich <math|f = 0>.
  </proof>

  <strong|5)> Sei

  <with|gr-mode|<tuple|group-edit|group-ungroup>|gr-frame|<tuple|scale|1cm|<tuple|0.5gw|0.5gh>>|gr-geometry|<tuple|geometry|1par|0.6par>|gr-grid|<tuple|empty>|gr-grid-old|<tuple|cartesian|<point|0|0>|1>|gr-edit-grid-aspect|<tuple|<tuple|axes|none>|<tuple|1|none>|<tuple|10|none>>|gr-edit-grid|<tuple|empty>|gr-edit-grid-old|<tuple|cartesian|<point|0|0>|1>|gr-text-at-halign|right|gr-arrow-end|\<gtr\>|gr-auto-crop|true|gr-text-at-valign|axis|<graphics||<with|text-at-valign|center|text-at-halign|center|<text-at|U|<point|-1|1>>>|<with|text-at-valign|center|text-at-halign|center|<text-at|U|<point|-1|0>>>|<with|text-at-valign|center|text-at-halign|center|<text-at|V|<point|0|0>>>|<with|text-at-valign|center|text-at-halign|center|<text-at|W|<point|1|1>>>|<with|text-at-valign|center|text-at-halign|center|<text-at|W|<point|1|0>>>|<with|arrow-end|\<gtr\>|<line|<point|-1|0.760964>|<point|-1.0|0.239036248180976>>>|<with|arrow-end|\<gtr\>|<line|<point|0|0.760964>|<point|0.0|0.239036248180976>>>|<with|arrow-end|\<gtr\>|<line|<point|1|0.760964>|<point|1.0|0.239036248180976>>>|<with|arrow-end|\<gtr\>|<line|<point|-0.750182|1>|<point|-0.249801561053049|1.0>>>|<with|arrow-end|\<gtr\>|<line|<point|-0.750182|0>|<point|-0.249801561053049|0.0>>>|<with|text-at-valign|center|text-at-halign|center|<text-at|0|<point|-2|0>>>|<with|text-at-valign|center|text-at-halign|center|<text-at|0|<point|2|1>>>|<with|text-at-valign|center|text-at-halign|center|<text-at|0|<point|2|0>>>|<with|text-at-valign|center|text-at-halign|center|<text-at|0|<point|-2.0|1.0>>>|<with|arrow-end|\<gtr\>|<line|<point|-1.79427|1>|<point|-1.24980156105305|1.0>>>|<with|arrow-end|\<gtr\>|<line|<point|-1.79427|0>|<point|-1.24980156105305|0.0>>>|<with|arrow-end|\<gtr\>|<line|<point|1.2988|1>|<point|1.79428495832782|1.0>>>|<with|arrow-end|\<gtr\>|<line|<point|1.2988|0>|<point|1.79428495832782|0.0>>>|<with|text-at-valign|center|text-at-halign|center|>|<with|text-at-valign|center|text-at-halign|center|<text-at|V|<point|0.0|1.0>>>|<with|arrow-end|\<gtr\>|<line|<point|0.249818|1>|<point|0.701200555629051|1.0>>>|<with|arrow-end|\<gtr\>|<line|<point|0.249818|0>|<point|0.701200555629051|0.0>>>|<with|text-at-valign|bottom|text-at-halign|center|<math-at|p|<point|0.5|1>>>|<with|text-at-valign|bottom|text-at-halign|center|<math-at|p|<point|0.5|0.0>>>|<with|text-at-valign|bottom|text-at-halign|center|<math-at|i|<point|-0.5|1>>>|<with|text-at-valign|bottom|text-at-halign|center|<math-at|i|<point|-0.5|0>>>|<with|text-at-valign|axis|text-at-halign|right|<math-at|f
  |<point|-1|0.5>>>|<with|text-at-valign|axis|text-at-halign|right|<math-at|g
  |<point|0|0.5>>>|<with|text-at-valign|axis|text-at-halign|right|<math-at|h
  |<point|1|0.5>>>>>

  ein kommutatives Diagramm von Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln
  mit exakten Zeilen und <math|f>, <math|g>, <math|h> positiv. Dann gilt
  <math|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|g|)>=tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>+tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|h|)>>.

  <\proof>
    Wir dürfen annehmen, dass <math|V \<cong\> U\<oplus\>W> (da
    <math|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|g|)>=tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|u<rsup|-1>
    g u|)>> für eine unitäre <math|G>-äquivariante Abbildung <math|u : V
    \<rightarrow\> U\<oplus\>W>). Dann ist <math|g> von der Form

    <\equation*>
      g=<matrix|<tformat|<table|<row|<cell|f>|<cell|k>>|<row|<cell|0>|<cell|h>>>>>
      : U\<oplus\>W\<longrightarrow\>U\<oplus\>W.
    </equation*>

    Für Abbildungen dieser Form ist die Aussage klar: Wähle isometrische,
    <math|G>-äquivariante Einbettungen <math|i :
    U\<rightarrow\>H\<otimes\>l<rsup|2><around*|(|G|)>> und
    <math|i<rprime|'>:W\<rightarrow\>H<rprime|'>\<otimes\>l<rsup|2><around*|(|G|)>>
    und Hilbertbasen <math|<around*|(|b<rsub|i>|)><rsub|i\<in\>I>> von
    <math|H> und <math|<around*|(|b<rprime|'><rsub|j>|)><rsub|j\<in\>J>> von
    <math|H<rprime|'>>. Dann ist die Konkatenation dieser Basen eine
    Hilbertbasis von <math|H\<oplus\>H<rprime|'>> und
    <math|i\<oplus\>i<rprime|'> : U\<oplus\>W\<rightarrow\><around*|(|H\<oplus\>H<rprime|'>|)>\<otimes\>l<rsup|2><around*|(|G|)>>
    eine isometrische Einbettung. Somit

    <\equation*>
      \;
    </equation*>

    <\eqnarray*>
      <tformat|<cwith|1|1|2|2|cell-halign|l>|<cwith|3|3|2|2|cell-halign|l>|<table|<row|<cell|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|g|)>=>|<cell|<big|sum><rsub|i\<in\>I><around*|\<langle\>|<overline|g><around*|(|b<rsub|i>\<otimes\>e|)>,b<rsub|i>\<otimes\>e|\<rangle\>>+<big|sum><rsub|j\<in\>J><around*|\<langle\>|<overline|g><around*|(|b<rprime|'><rsub|i>\<otimes\>e|)>,b<rprime|'><rsub|i>\<otimes\>e|\<rangle\>>>|<cell|>>|<row|<cell|=>|<cell|<big|sum><rsub|i\<in\>I><around*|\<langle\>|<overline|f><around*|(|b<rsub|i>\<otimes\>e|)>,b<rsub|i>\<otimes\>e|\<rangle\>>+<big|sum><rsub|j\<in\>J><around*|\<langle\>|<overline|h><around*|(|b<rprime|'><rsub|i>\<otimes\>e|)>,b<rprime|'><rsub|i>\<otimes\>e|\<rangle\>>+<big|sum><rsub|j\<in\>J><around*|\<langle\>|<overline|k><around*|(|b<rprime|'><rsub|i>\<otimes\>e|)>,b<rprime|'><rsub|i>\<otimes\>e|\<rangle\>>>|<cell|>>|<row|<cell|=>|<cell|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>+tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|h|)>+0.>|<cell|>>>>
    </eqnarray*>
  </proof>

  <strong|6)> Für einen Morphismus <math|f : V \<rightarrow\> W> von
  Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln gilt

  <\equation*>
    tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f<rsup|<math-up|*>>f|)>=tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f
    f<rsup|<math-up|*>>|)>.
  </equation*>

  <\proof>
    Sei <math|f = u <around*|\||f|\|>> die Polarzerlegung von <math|f> in
    <with|color|dark magenta|TODO>. Dann gilt

    <\equation*>
      tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f
      f<rsup|\<ast\>>|)>=tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|u
      <around*|\||f|\|><rsup|2> u<rsup|-1>|)>=tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|<around*|\||f|\|><rsup|2>|)>=tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f<rsup|\<ast\>>f|)>.
    </equation*>
  </proof>

  <\remark*>
    Sei <math|H\<less\>G> eine Untergruppe mit endlichem Index
    <math|<around*|[|G :H|]>>. Dann kann man jedes
    Hilbert-<math|\<cal-N\><around*|(|G|)>>-Modul auch als
    Hilbert-<math|\<cal-N\><around*|(|H|)>>-Modul auffassen (durch
    Einschränkung der Gruppenwirkung). Wähle Repräsentanten
    <math|x<rsub|1>,\<ldots\>,x<rsub|k>\<in\>G> der <math|H>-Orbits von
    <math|G>, <math|k=<around*|[|G :H|]>>. Sei \ <math|i :
    V\<hookrightarrow\>H\<otimes\>l<rsup|2><around*|(|G|)>> eine
    isometrische, <math|G>-äquivariante Einbettung. Man erhält eine
    isometrische <math|H>-äquivariante Einbettung durch Nachschalten
    folgender Abbildung:

    <\eqnarray*>
      <tformat|<table|<row|<cell|H\<otimes\>l<rsup|2><around*|(|G|)>>|<cell|\<rightarrow\>>|<cell|<around*|(|<big|oplus><rsub|g
      H\<in\>G/H>H|)>\<otimes\>l<rsup|2><around*|(|H|)>\<cong\><big|oplus><rsub|i=1,\<ldots\>,k><around*|(|H\<otimes\>l<rsup|2><around*|(|H|)>\<nocomma\>\<nocomma\>|)>>>|<row|<cell|h\<otimes\>g>|<cell|\<mapsto\>>|<cell|<around*|(|0,\<ldots\>,h\<otimes\>
      x<rsub|j><rsup|-1>g,\<ldots\>,0|)><space|1em><math-up|für
      <math|g\<in\>x<rsub|j>H>>.>>>>
    </eqnarray*>
  </remark*>

  <strong|8)> Sei <math|H\<less\>G> eine Untergruppe mit endlichem Index
  <math|<around*|[|G :H|]>>. Sei <math|f : V \<rightarrow\> V> ein positiver
  Endomorphismus eines Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduls
  <math|V>. Dann gilt <math|dim<rsub|\<cal-N\><around*|(|H|)>><around*|(|f|)>=<around*|[|g
  :H|]>\<cdot\>dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>>.

  <\proof>
    Sei <math|<around*|(|b<rsub|i>|)><rsub|i\<in\>I>> eine Basis von
    <math|H>. Dann ist <math|<around*|(|0,\<ldots\>,b<rsub|i>,\<ldots\>,0|)><rsub|i\<in\>I,j=1,\<ldots\>,k>>
    eine Hilbertbasis von <math|<big|oplus><rsub|g H\<in\>G/H>H> (dabei steht
    das <math|b<rsub|i>> an der <math|j>-ten Stelle) und es gilt

    <\eqnarray*>
      <tformat|<table|<row|<cell|tr<rsub|\<cal-N\><around*|(|H|)>><around*|(|f|)>>|<cell|=>|<cell|<big|sum><rsub|j=1,\<ldots\>,k><big|sum><rsub|i\<in\>I><around*|\<langle\>|<overline|f<rsub|H>><around*|(|<around*|(|0,\<ldots\>,b<rsub|i>,\<ldots\>,0|)>\<otimes\>e|)>,<around*|(|0,\<ldots\>,b<rsub|i>,\<ldots\>,0|)>\<otimes\>e|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<big|sum><rsub|j=1,\<ldots\>,k><big|sum><rsub|i\<in\>I><around*|\<langle\>|<overline|f<rsub|G>><around*|(|b<rsub|i>\<otimes\>x<rsub|j>|)>\<nocomma\>,b<rsub|i>\<otimes\>x<rsub|j>|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|<big|sum><rsub|j=1,\<ldots\>,k><big|sum><rsub|i\<in\>I><around*|\<langle\>|<overline|f<rsub|G>><around*|(|b<rsub|i>\<otimes\>e|)>\<nocomma\>,b<rsub|i>\<otimes\>e|\<rangle\>>>>|<row|<cell|>|<cell|=>|<cell|k\<cdot\>tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|f|)>.>>>>
    </eqnarray*>
  </proof>

  <\definition*>
    <dueto|[L], 1.10>Die <strong|Von-Neumann-Dimension> eines
    Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduls <math|V> ist

    <\equation*>
      dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|V|)>\<assign\>tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|id<rsub|V>|)><space|2em>\<in\>
      <around*|[|0,\<infty\>|]>.
    </equation*>
  </definition*>

  <\lemma*>
    Wenn <math|G> endlich ist, so gilt <math|dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|V|)>=<frac|1|<around*|\||G|\|>>\<cdot\>dim<rsub|\<bbb-C\>><around*|(|V|)>>
    für alle Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln <math|V>.
  </lemma*>

  <\proof>
    Wir wählen folgende Einbettung:

    <\equation*>
      i : V\<rightarrow\>V\<otimes\>l<rsup|2><around*|(|G|)>,<space|2em>v\<mapsto\><tfrac|1|<around*|\||G|\|>>\<cdot\><big|sum><rsub|g\<in\>G><around*|(|g.v|)>\<otimes\>g<rsup|-1>.
    </equation*>

    Man rechnet leicht nach, dass <math|i> isometrisch ist. Auÿerdem ist
    <math|i> <math|G>-äquivariant:

    <\equation*>
      i<around*|(|h.v|)>=<tfrac|1|<around*|\||G|\|>>\<cdot\><big|sum><rsub|g\<in\>G><around*|(|g
      h.v|)>\<otimes\>g<rsup|-1>=<tfrac|1|<around*|\||G|\|>>\<cdot\><big|sum><rsub|g\<in\>G><around*|(|g.v|)>\<otimes\><around*|(|h
      g<rsup|-1>|)>=h.<around*|(|<tfrac|1|<around*|\||G|\|>>\<cdot\><big|sum><rsub|g\<in\>G><around*|(|g.v|)>\<otimes\>g<rsup|-1>|)>=h.i<around*|(|v|)>.
    </equation*>

    Sei <math|<around*|(|b<rsub|i>|)><rsub|i\<in\>I>> eine Hilbertbasis von
    <math|V>. Dann gilt

    <\equation*>
      dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|V|)>=<big|sum><rsub|i\<in\>I><around*|\<langle\>|pr<rsub|im<around*|(|i|)>><around*|(|b<rsub|i>\<otimes\>e|)>,b<rsub|i>\<otimes\>e|\<rangle\>>=<big|sum><rsub|i\<in\>I><around*|\<langle\>|<tfrac|1|<around*|\||G|\|>>\<cdot\><big|sum><rsub|g\<in\>G>b<rsub|i>\<otimes\>g,b<rsub|<with|math-condensed|true|>i>\<otimes\>e|\<rangle\>>=<big|sum><rsub|i\<in\>I><tfrac|1|<around*|\||G|\|>>=<tfrac|1|<around*|\||G|\|>>\<cdot\>dim<rsub|\<bbb-C\>><around*|(|V|)>.<with|math-display|false|>
    </equation*>
  </proof>

  <\example*>
    <dueto|[L], 1.11>Erinnerung: Wir haben gesehen, dass wir
    <math|l<rsup|2><around*|(|\<bbb-Z\><rsup|n>|)>> mit
    <math|L<rsup|2><around*|(|T<rsup|n>|)>> und
    <math|\<cal-N\><around*|(|\<bbb-Z\>|)>> mit
    <math|L<rsup|\<infty\>><around*|(|T<rsup|n>|)>> identifizieren können,
    wobei <math|L<rsup|\<infty\>><around*|(|T<rsup|n>|)>> auf
    <math|L<rsup|2><around*|(|T<rsup|n>|)>> durch punktweise Multiplikation
    wirkt:<math|> Für <math|g\<in\>L<rsup|\<infty\>><around*|(|T<rsup|n>|)>>
    ist

    <\equation*>
      <around*|(|g.f|)><around*|(|<wide|x|\<vect\>>|)>\<assign\>M<rsub|g><around*|(|f|)><around*|(|<wide|x|\<vect\>>|)>\<assign\>g<around*|(|<wide|x|\<vect\>>|)>\<cdot\>f<around*|(|<wide|x|\<vect\>>|)>.
    </equation*>

    Unter dieser Identifikation entspricht die Von-Neumann-Spur dem Integral
    über <math|T<rsup|n>>:

    <\equation*>
      tr<rsub|\<cal-N\><around*|(|\<bbb-Z\>|)>><around*|(|g|)>=<big|int><rsub|T<rsup|n>>g
      <math-up|d>\<mu\>.
    </equation*>

    Sei nun <math|X \<subseteq\> T<rsup|n>> messbar,
    <math|\<chi\><rsub|X>\<in\>L<rsup|\<infty\>><around*|(|T<rsup|n>|)>> die
    charakteristische Funktion von <math|X>. Dann ist

    <\equation*>
      M<rsub|\<chi\><rsub|X>> : L<rsup|2><around*|(|T<rsup|n>|)>\<rightarrow\>L<rsup|2><around*|(|T<rsup|n>|)>,<space|1em>f\<mapsto\><around*|(|<wide|x|\<vect\>>\<mapsto\>f<around*|(|<wide|x|\<vect\>>|)>\<cdot\>\<chi\><rsub|X><around*|(|<wide|x|\<vect\>>|)>|)>
    </equation*>

    <math|\<bbb-Z\><rsup|n>>-äquivariant und
    <math|im<around*|(|M<rsub|\<chi\><rsub|X>>|)>> ein
    Hilbert-<math|\<cal-N\><around*|(|\<bbb-Z\>|)>>-Modul mit

    <\equation*>
      dim<rsub|\<cal-N\><around*|(|\<bbb-Z\>|)>><around*|(|im<around*|(|M<rsub|\<chi\><rsub|X>>|)>|)>=<big|int><rsub|T<rsup|n>>\<chi\><rsub|X>
      <math-up|d>\<mu\>=\<mu\><around*|(|X|)>.
    </equation*>
  </example*>

  <\theorem*>
    <dueto|[L], 1.12> <em|<strong|1)> Für einen
    Hilbert-<math|\<cal-N\><around*|(|G|)>>-Modul <math|V> gilt>
    <math|dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|V|)>=0>
    \ <math|\<Longleftrightarrow\>> \ <math|V=0>
  </theorem*>

  <\proof>
    <math|dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|V|)>=0>
    \ <math|\<Longleftrightarrow\>> \ <math|tr<rsub|\<cal-N\><around*|(|G|)>><around*|(|id<rsub|V>|)>=0>
    \ <math|\<Longleftrightarrowlim\><rsup|<math-up|1.9 (3)>>>
    \ <math|id<rsub|V>=0> \ <math|\<Longleftrightarrow\>> \ <math|V=0>
  </proof>

  <strong|2)> Für eine kurze, schwach exakte Sequenz
  <math|0\<rightarrow\>U\<rightarrow\>V\<rightarrow\>W\<rightarrow\>0> von
  Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln gilt

  <\equation*>
    dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|V|)>=dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|U|)>+dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|W|)>.
  </equation*>

  <\proof>
    Wir können annehmen, dass die Sequenz exakt (und nicht nur schwach exakt
    ist). Dann folgt die Aussage aus Satz 1.9 (5).
  </proof>

  <strong|6)> Sei <math|H\<less\>G> eine Untergruppe mit endlichem Index
  <math|<around*|[|G :H|]>> und <math|V> ein
  Hilbert-<math|\<cal-N\><around*|(|G|)>>-Modul. Dann ist
  <math|dim<rsub|\<cal-N\><around*|(|H|)>><around*|(|V|)>=<around*|[|G
  :H|]>\<cdot\>dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|V|)>>.

  <\proof>
    Folgt aus Satz 1.9, 8)
  </proof>

  <\remark*>
    Endlich erzeugte Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduln besitzen
    endliche Dimension. Die Umkehrung gilt aber nicht:
  </remark*>

  <\example*>
    <dueto|[L], 1.14>Für ein Interval <math|I \<subset\> <around*|[|0,1|]>>
    sei <math|\<chi\><rsub|I>\<in\>L<rsup|\<infty\>><around*|(|S<rsup|1>|)>\<cong\>\<cal-N\><around*|(|\<bbb-Z\>|)>>
    die charakteristische Funktion von <math|<around*|{|e<rsup|2i\<pi\>x> \|
    x\<in\>I|}>\<subset\>S<rsup|1>>. Definiere

    <\equation*>
      U\<assign\><big|oplus><rsup|\<infty\>><rsub|n=1>im<around*|(|\<chi\><rsub|<around*|[|0,2<rsup|-n>|]>>|)>,<space|2em>V\<assign\><big|oplus><rsup|\<infty\>><rsub|n=1>im<around*|(|\<chi\><rsub|<around*|[|<frac|1|n+1>,<frac|1|n>|]>>|)>.
    </equation*>

    Es gilt

    <\equation*>
      dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|U|)>=<big|sum><rsup|\<infty\>><rsub|n=1>dim<rsub|\<cal-N\><around*|(|G|)>><around*|(|im<around*|(|\<chi\><rsub|<around*|[|0,2<rsup|-n>|]>>|)>|)>=<big|sum><rsup|\<infty\>><rsub|n=1>\<mu\><around*|(|<around*|{|e<rsup|i\<pi\>x>
      \| x\<in\><around*|[|0,2<rsup|-n>|]>|}>|)>=<big|sum><rsup|\<infty\>><rsub|n=1><around*|(|<tfrac|1|n>-<tfrac|1|n+1>|)>=1,
    </equation*>

    wobei die erste Gleichheit aus [L], Thm 1.12, 2) und 3) verwendet. Aus
    einer analogen Rechnung folgt d<math|im<rsub|\<cal-N\><around*|(|G|)>><around*|(|U|)>=1>.
    Nun ist <math|U\<cong\>L<rsup|2><around*|(|S<rsup|1>|)>\<cong\>l<rsup|2><around*|(|\<bbb-Z\>|)>>
    und somit insbesondere ein endlich erzeugtes
    Hilbert-<math|\<cal-N\><around*|(|G|)>>-Modul. Obwohl <math|V> die
    gleiche Von-Neumann-Dimension wie <math|U> besitzt, ist <math|V> aber
    nicht endlich erzeugt. Um das einzusehen, benötigen wir folgende

    <\definition*>
      Die <strong|Dimension mit Wert im Zentrum> eines endlich erzeugten
      Hilbert-<math|\<cal-N\><around*|(|G|)>>-Moduls <math|V> mit
      isometrischer <math|G>-Einbettung <math|i :
      V\<hookrightarrow\>\<bbb-C\><rsup|n>\<otimes\>l<rsup|2><around*|(|G|)>>
      ist

      <\eqnarray*>
        <tformat|<table|<row|<cell|dim<rsup|c><rsub|\<cal-N\><around*|(|G|)>><around*|(|V|)>\<assign\>>|<cell|<big|sum><rsub|i=1><rsup|n>>|<cell|<around*|(|l<rsup|2><around*|(|G|)>\<cong\>span<around*|{|e<rsub|i>|}>\<otimes\>l<rsup|2><around*|(|G|)>\<hookrightarrow\>\<bbb-C\><rsup|n>\<otimes\>l<rsup|2><around*|(|G|)><long-arrow|\<rubber-rightarrow\>|pr<rsub|im<around*|(|i|)>>>im<around*|(|i|)>
        \<hookrightarrow\>|\<nobracket\>>>>|<row|<cell|>|<cell|>|<cell|<space|1em><around*|\<nobracket\>|\<hookrightarrow\>
        \<bbb-C\><rsup|n>\<otimes\>l<rsup|2><around*|(|G|)><long-arrow|\<rubber-rightarrow\>|pr<rsub|span<around*|{|e<rsub|i>|}>\<otimes\>l<rsup|2><around*|(|G|)>>>span<around*|{|e<rsub|i>|}>\<otimes\>l<rsup|2><around*|(|G|)>\<cong\>l<rsup|2><around*|(|G|)>|)><space|1em>\<in\>\<cal-N\><around*|(|G|)>.>>>>
      </eqnarray*>

      Man zeigt wie bei der Definition der Von-Neumann-Spur, dass diese
      unabhängig von den Wahlen ist.
    </definition*>

    Die einzelnen Summanden sind dabei positive Operatoren aus
    <math|\<cal-N\><around*|(|G|)>>. Es gilt
    <math|dim<rsup|c><rsub|\<cal-N\><around*|(|G|)>><around*|(|U\<oplus\>W|)>
    = dim<rsup|c><rsub|\<cal-N\><around*|(|G|)>><around*|(|U|)>+dim<rsup|c><rsub|\<cal-N\><around*|(|G|)>><around*|(|W|)>>
    für endlich erzeuge <math|G>-Moduln <math|U> und <math|W>. In unserem
    Setting entsprechen positive Operatoren aus
    <math|\<cal-N\><around*|(|\<bbb-Z\>|)>> fast-überall positiven Funktionen
    aus <math|L<rsup|\<infty\>><around*|(|S<rsup|1>|)>>.

    Angenommen, <math|V> ist endlich erzeugt. Dann gibt es eine isometrische
    \ <math|G>-Einbettung <math|V \<hookrightarrow\>
    \<bbb-C\><rsup|k>\<otimes\>l<rsup|2><around*|(|\<bbb-Z\>|)>> mit
    <math|k\<in\>\<bbb-N\>>. Da <math|<big|oplus><rsup|k+1><rsub|n=1>im<around*|(|\<chi\><rsub|<around*|[|0,2<rsup|-n>|]>>|)>>
    ein direkter Summand von <math|V> und <math|V> ein direkter Summand von
    <math|\<bbb-C\><rsup|k>\<otimes\>l<rsup|2><around*|(|\<bbb-Z\>|)>> ist,
    gilt

    <\equation*>
      <big|sum><rsub|n=1><rsup|k+1>\<chi\><rsub|<around*|[|0,2<rsup|-n>|]>>=dim<rsup|c><rsub|\<cal-N\><around*|(|G|)>><around*|(|<big|oplus><rsup|k+1><rsub|n=1>im<around*|(|\<chi\><rsub|<around*|[|0,2<rsup|-n>|]>>|)>|)>\<leqslant\>dim<rsup|c><rsub|\<cal-N\><around*|(|G|)>><around*|(|V|)>\<leqslant\>dim<rsup|c><rsub|\<cal-N\><around*|(|G|)>><around*|(|\<bbb-C\><rsup|k>\<otimes\>l<rsup|2><around*|(|\<bbb-Z\>|)>|)>=c<rsub|k><space|1em>\<in\>L<rsup|\<infty\>><around*|(|S<rsup|1>|)>,
    </equation*>

    wobei <math|c<rsub|k>\<equiv\>k : S<rsup|1>\<rightarrow\>\<bbb-C\>>
    konstant ist. Die Funktion <math|<big|sum><rsub|n=1><rsup|k+1>\<chi\><rsub|<around*|[|0,2<rsup|-n>|]>>>
    aber ist gleich <math|k+1> im Bereich <math|<around*|{|e<rsup|2i\<pi\>x>
    \| x\<in\><around*|[|0,2<rsup|-<around*|(|k+1|)>>|]>|}>>. Widerspruch.
  </example*>

  \;

  <strong|[L]><space|1em>W. Lück, <em|L<rsup|2>-invariants: Theory and
  applications to geometry and K-theory>, Ergebnisse der Mathematik und ihrer
  Grenzgebiete <strong|44>, Springer-Verlag.

  <strong|[E]><nbsp> B. Eckmann, <em|Introduction to L<rsup|2>-methods in
  topology: Reduced L<rsup|2>-homology, harmonic chains, L<rsup|2>-Betti
  numbers>, Israel J. of Math. <strong|117> (2000), 183-219.

  [R] W. Rudin, <em|Functional Analysis (2nd edition)>, 1991\ 
</body>