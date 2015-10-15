<TeXmacs|1.99.2>

<style|generic>

<\body>
  <section*|Session 1>

  <subsection*|Exercise 1>

  <\itemize>
    <item>A musical note. The two objects are its duration and pitch.

    <item>A vector. The two objects are its angle and magnitude
  </itemize>

  <subsection*|Exercise 2>

  One could fill a tub with water. The surface of the water will be level.

  <section*|Article I>

  <subsection*|Exercise 1>

  TODO: Insert figure.

  <subsection*|Exercise 2>

  <\math>
    2<rsup|3>=8
  </math>

  <subsection*|Exercise 3>

  <math|3<rsup|3>=27>

  <subsection*|Exercise 4>

  <math|3<rsup|2>=9>

  <subsection*|Exercise 5>

  <math|2<rsup|2>=4>

  <subsection*|Exercise 6>

  <math|10>

  The general formula for <math|n> elements is
  <math|<big|sum><rsub|k=0><rsup|n><choose|n|k>*k<rsup|n-k>>.

  <subsection*|Exercise 7>

  <math|3>

  <subsection*|Exercise 8>

  No.

  <subsection*|Exercise 9>

  <math|12>

  If <math|A> has <math|a> elements and <math|B>, <math|b>, then there are
  <math|<frac|a!|<around*|(|a-b|)>!>> injections from <math|B> to <math|A>.
  \ In the other direction, for each of these, there are <math|b<rsup|a-b>>
  maps back. Whence there are <math|<frac|a!|<around*|(|a-b|)>!>*b<rsup|a-b>>
  such pairs of maps.

  <section*|Session 2>

  No exercises.

  <section*|Session 3>

  <subsection*|Exercise 1>

  <\enumerate-alpha>
    <item><math|A\<rightarrow\>B>

    <item>does't make sense

    <item><math|A\<rightarrow\>A>
  </enumerate-alpha>

  <subsection*|Exercise 2>

  TODO: Learn how to make these diagrams.

  <section*|Article II>

  <subsection*|Exercise 1>

  <\description>
    <item*|R>We must show that there is a map <math|g\<of\>A\<rightarrow\>A>
    st <math|g\<circ\>1<rsub|A>=1<rsub|A>> and
    <math|1<rsub|A>\<circ\>g=1<rsub|A>>. Take <math|g=1<rsub|A>>.

    <item*|S>We must show that there is a map
    <math|g<rsup|-1>\<of\>A\<rightarrow\>B> st
    <math|g<rsup|-1>\<circ\>g=1<rsub|B>> and
    <math|g\<circ\>g<rsup|-1>=1<rsub|A>>. Take <math|g<rsup|-1>=f>.

    <item*|T>We must show that there is a map <math|g\<of\>C\<rightarrow\>A>
    st <math|g\<circ\><around*|(|k\<circ\>f|)>=1<rsub|A>> and
    <math|<around*|(|k\<circ\>f|)>\<circ\>g=1<rsub|C>>. Take
    <math|g=f<rsup|-1>\<circ\>k<rsup|-1>>. Then

    <\eqnarray*>
      <tformat|<table|<row|<cell|f<rsup|-1>\<circ\>k<rsup|-1>\<circ\>k\<circ\>f>|<cell|=>|<cell|f<rsup|-1>\<circ\>1<rsub|B>\<circ\>f>>|<row|<cell|>|<cell|=>|<cell|f<rsup|-1>\<circ\>f>>|<row|<cell|>|<cell|=>|<cell|1<rsub|A>>>>>
    </eqnarray*>

    and

    <\eqnarray*>
      <tformat|<table|<row|<cell|k\<circ\>f\<circ\>f<rsup|-1>\<circ\>k<rsup|-1>>|<cell|=>|<cell|k\<circ\>1<rsub|B>\<circ\>k<rsup|-1>>>|<row|<cell|>|<cell|=>|<cell|k\<circ\>k<rsup|-1>>>|<row|<cell|>|<cell|=>|<cell|1<rsub|C>>>>>
    </eqnarray*>
  </description>

  <subsection*|Exercise 2>

  <\eqnarray*>
    <tformat|<table|<row|<cell|1<rsub|A>>|<cell|=>|<cell|1<rsub|A>>>|<row|<cell|g\<circ\>f>|<cell|=>|<cell|k\<circ\>f>>|<row|<cell|g\<circ\>f\<circ\>g>|<cell|=>|<cell|k\<circ\>f\<circ\>g>>|<row|<cell|g\<circ\>1<rsub|B>>|<cell|=>|<cell|k\<circ\>1<rsub|B>>>|<row|<cell|g>|<cell|=>|<cell|k>>>>
  </eqnarray*>

  <subsection*|Exercise 3>

  <\enumerate-alpha>
    <item>

    <\eqnarray*>
      <tformat|<table|<row|<cell|f\<circ\>h>|<cell|=>|<cell|f\<circ\>k>>|<row|<cell|f<rsup|-1>\<circ\>f\<circ\>h>|<cell|=>|<cell|f<rsup|-1>\<circ\>f\<circ\>k>>|<row|<cell|1<rsub|A>\<circ\>h>|<cell|=>|<cell|1<rsub|A>\<circ\>k>>|<row|<cell|h>|<cell|=>|<cell|k>>>>
    </eqnarray*>

    <item>

    <\eqnarray*>
      <tformat|<table|<row|<cell|h\<circ\>f>|<cell|=>|<cell|k\<circ\>f>>|<row|<cell|h\<circ\>f\<circ\>f<rsup|-1>>|<cell|=>|<cell|k\<circ\>f\<circ\>f<rsup|-1>>>|<row|<cell|h\<circ\>1<rsub|B>>|<cell|=>|<cell|k\<circ\>1<rsub|B>>>|<row|<cell|h>|<cell|=>|<cell|k>>>>
    </eqnarray*>

    <item>Let <math|A=<around*|{|true,false|}>>,
    <math|f\<of\>A\<rightarrow\>A\<assign\>\<lambda\>x.not x>,
    <math|h\<of\>A\<rightarrow\>A\<assign\>\<lambda\>x.true>, and
    <math|k\<of\>A\<rightarrow\>A\<assign\>\<lambda\>x.false>. Then
    <math|h\<circ\>f=f\<circ\>k=true> for all <math|x\<in\>A>, yet
    <math|h\<neq\>k>.
  </enumerate-alpha>

  <subsection*|Exercise 4>

  <\enumerate-numeric>
    <item><math|f<rsup|-1>\<of\>\<bbb-R\>\<rightarrow\>\<bbb-R\>\<assign\>\<lambda\>y.<frac|y-7|3>>

    <item><math|g<rsup|-1>\<of\>\<bbb-R\><rsub|\<geq\>0>\<rightarrow\>\<bbb-R\><rsub|\<geq\>0>\<assign\>\<lambda\>y.<sqrt|y>>

    <item>not invertible

    <item>not invertible

    <item>not invertible, unless we restrict
    <math|l\<of\>\<bbb-R\><rsub|\<geq\>0>\<rightarrow\><around*|(|0,1|]>>.
    Then <math|l<rsup|-1>\<of\><around*|(|0,1|]>\<rightarrow\>\<bbb-R\><rsub|\<geq\>0>=\<lambda\>y.<frac|1|y>-1>.
  </enumerate-numeric>

  <subsection*|Exercise 5>

  There are <math|6> maps <math|f>. There are <math|8> maps <math|g>.

  <subsection*|Pick's Formula>

  <tabular*|<tformat|<table|<row|<cell|Interior Vertices>|<cell|Boundary
  Vertices>|<cell|Area>>|<row|<cell|0>|<cell|3>|<cell|<math|1/2>>>|<row|<cell|0>|<cell|4>|<cell|<math|1>>>|<row|<cell|0>|<cell|5>|<cell|<math|3/2>>>|<row|<cell|0>|<cell|6>|<cell|<math|2>>>|<row|<cell|1>|<cell|3>|<cell|<math|3/2>>>|<row|<cell|1>|<cell|4>|<cell|<math|2>>>|<row|<cell|1>|<cell|5>|<cell|<math|5/2>>>|<row|<cell|1>|<cell|6>|<cell|<math|3>>>|<row|<cell|1>|<cell|7>|<cell|<math|7/2>>>|<row|<cell|1>|<cell|8>|<cell|<math|4>>>|<row|<cell|2>|<cell|3>|<cell|<math|5/2>>>|<row|<cell|2>|<cell|4>|<cell|<math|3>>>|<row|<cell|2>|<cell|5>|<cell|>>|<row|<cell|2>|<cell|10>|<cell|<math|6>>>>>>

  <math|g\<of\>P\<rightarrow\>\<bbb-R\>\<assign\>\<lambda\><around*|(|i,b|)>.<frac|b|2>+i-1>

  <subsection*|Exercise 6>

  <\proposition*>
    If the map <math|f\<of\>A\<rightarrow\>B> has a retraction, then for any
    map <math|g\<of\>A\<rightarrow\>T>, there is a map
    <math|t\<of\>B\<rightarrow\>T> for which <math|t\<circ\>f=g>.

    <\proof>
      The assumption means that there is some map
      <math|r\<of\>B\<rightarrow\>A> such that <math|r\<circ\>f=1<rsub|A>>.
      \ Now, the map <math|g\<circ\>r\<of\>B\<rightarrow\>T> has at least the
      required type. \ Let <math|t=g\<circ\>r>. \ Then

      <\eqnarray*>
        <tformat|<table|<row|<cell|<around*|(|g\<circ\>r|)>\<circ\>f>|<cell|=>|<cell|g\<circ\><around*|(|r\<circ\>f|)>>>|<row|<cell|>|<cell|=>|<cell|g\<circ\>1<rsub|A>>>|<row|<cell|>|<cell|=>|<cell|g>>>>
      </eqnarray*>

      as required.
    </proof>
  </proposition*>

  <subsection*|Exercise 7>

  <\proposition*>
    Suppose the map <math|f\<of\>A\<rightarrow\>B> has a section. \ Then for
    any set <math|T> and any pair <math|t<rsub|1>\<of\>B\<rightarrow\>T>,
    <math|t<rsub|2>\<of\>B\<rightarrow\>T> of maps from <math|B> to <math|T>,
    if <math|t<rsub|1>\<circ\>f=t<rsub|2>\<circ\>f> then
    <math|t<rsub|1>=t<rsub|2>>.

    <\proof>
      The assumption means that there is some map
      <math|s\<of\>B\<rightarrow\>A> such that <math|f\<circ\>s=1<rsub|B>>.
      \ Then

      <\eqnarray*>
        <tformat|<table|<row|<cell|t<rsub|1>>|<cell|=>|<cell|t<rsub|1>\<circ\>1<rsub|B>>>|<row|<cell|>|<cell|=>|<cell|t<rsub|1>\<circ\><around*|(|f\<circ\>s|)>>>|<row|<cell|>|<cell|=>|<cell|<around*|(|t<rsub|1>\<circ\>f|)>\<circ\>s>>|<row|<cell|>|<cell|=>|<cell|<around*|(|t<rsub|2>\<circ\>f|)>\<circ\>s>>|<row|<cell|>|<cell|=>|<cell|t<rsub|2>\<circ\><around*|(|f\<circ\>s|)>>>|<row|<cell|>|<cell|=>|<cell|t<rsub|2>\<circ\>1<rsub|B>>>|<row|<cell|>|<cell|=>|<cell|t<rsub|2>>>>>
      </eqnarray*>

      as required.
    </proof>
  </proposition*>

  <subsection*|Exercise 8>

  <\proposition*>
    If <math|f\<of\>A\<rightarrow\>B> has a section and if
    <math|g\<of\>B\<rightarrow\>C> has a section, then
    <math|g\<circ\>f\<of\>A\<rightarrow\>C> has a section.

    <\proof>
      Let <math|r<rsub|f>> and <math|r<rsub|g>> be the respective sections,
      and <math|r\<of\>C\<rightarrow\>A\<assign\>r<rsub|f>\<circ\>r<rsub|g>>.
      \ Then

      <\eqnarray*>
        <tformat|<table|<row|<cell|r\<circ\><around*|(|g\<circ\>f|)>>|<cell|=>|<cell|<around*|(|r<rsub|f>\<circ\>r<rsub|g>|)>\<circ\><around*|(|g\<circ\>f|)>>>|<row|<cell|>|<cell|=>|<cell|r<rsub|f>\<circ\><around*|(|r<rsub|g>\<circ\>g|)>\<circ\>f>>|<row|<cell|>|<cell|=>|<cell|r<rsub|f>\<circ\>1<rsub|B>\<circ\>f>>|<row|<cell|>|<cell|=>|<cell|r<rsub|f>\<circ\>f>>|<row|<cell|>|<cell|=>|<cell|1<rsub|A>>>>>
      </eqnarray*>

      as required.
    </proof>
  </proposition*>

  <subsection*|Exercise 9>

  <\proposition*>
    Suppose <math|r> is a retraction of <math|f> (equivalently <math|f> is a
    section of <math|r>) and let <math|e=f\<circ\>r>. \ Show that <math|e> is
    idempotent. \ (As we'll see later, in most categories it is true
    conversely that all idempotents can be `split' in this way.) \ Show that
    if <math|f> is an isomorphism, then <math|e> is the identity.

    <\proof>
      (Let <math|f\<of\>A\<rightarrow\>B> and <math|r\<of\>B\<rightarrow\>A>.
      \ Then <math|e\<of\>B\<rightarrow\>B>.) \ Now

      <\eqnarray*>
        <tformat|<table|<row|<cell|e\<circ\>e>|<cell|=>|<cell|<around*|(|f\<circ\>r|)>\<circ\><around*|(|f\<circ\>r|)>>>|<row|<cell|>|<cell|=>|<cell|f\<circ\><around*|(|r\<circ\>f|)>\<circ\>r>>|<row|<cell|>|<cell|=>|<cell|f\<circ\>1<rsub|A>\<circ\>r>>|<row|<cell|>|<cell|=>|<cell|f\<circ\>r>>|<row|<cell|>|<cell|=>|<cell|e>>>>
      </eqnarray*>

      so indeed <math|e> is idempotent. \ Now suppose <math|f> is an
      isomorphism. \ Then there is a map <math|f<rsup|-1>\<of\>B\<rightarrow\>A>
      such that <math|f<rsup|-1>\<circ\>f=1<rsub|A>> and
      <math|f\<circ\>f<rsup|-1>=1<rsub|B>>. \ In fact <math|r=f<rsup|-1>>:

      <\eqnarray*>
        <tformat|<table|<row|<cell|r\<circ\>f>|<cell|=>|<cell|1<rsub|A>>>|<row|<cell|<around*|(|r\<circ\>f|)>\<circ\>f<rsup|-1>>|<cell|=>|<cell|1<rsub|A>\<circ\>f<rsup|-1>>>|<row|<cell|r\<circ\><around*|(|f\<circ\>f<rsup|-1>|)>>|<cell|=>|<cell|f<rsup|-1>>>|<row|<cell|r\<circ\>1<rsub|B>>|<cell|=>|<cell|f<rsup|-1>>>|<row|<cell|r>|<cell|=>|<cell|f<rsup|-1>>>>>
      </eqnarray*>

      Finally,

      <\eqnarray*>
        <tformat|<table|<row|<cell|e\<circ\>e>|<cell|=>|<cell|e>>|<row|<cell|f\<circ\>r\<circ\>e>|<cell|=>|<cell|f\<circ\>r>>|<row|<cell|f<rsup|-1>\<circ\>f\<circ\>r\<circ\>e>|<cell|=>|<cell|f<rsup|-1>\<circ\>f\<circ\>r>>|<row|<cell|1<rsub|A>\<circ\>r\<circ\>e>|<cell|=>|<cell|1<rsub|A>\<circ\>r>>|<row|<cell|r\<circ\>e>|<cell|=>|<cell|r>>|<row|<cell|r<rsup|-1>\<circ\>r\<circ\>e>|<cell|=>|<cell|r<rsup|-1>\<circ\>r>>|<row|<cell|1<rsub|B>\<circ\>e>|<cell|=>|<cell|1<rsub|B>>>|<row|<cell|e>|<cell|=>|<cell|1<rsub|B>>>>>
      </eqnarray*>

      as required.
    </proof>
  </proposition*>

  <subsection*|Exercise 10>

  <\proposition*>
    If <math|A<above|\<rightarrow\>|f>B<above|\<rightarrow\>|g>C> are both
    isomorphisms, then <math|g\<circ\>f> is an isomorphism too, and
    <math|<around*|(|g\<circ\>f|)><rsup|-1>=f<rsup|-1>\<circ\>g<rsup|-1>>.

    <\proof>
      We show that <math|f<rsup|-1>\<circ\>g<rsup|-1>> is both a retraction
      and a section for <math|g\<circ\>f>.

      <\eqnarray*>
        <tformat|<table|<row|<cell|<around*|(|f<rsup|-1>\<circ\>g<rsup|-1>|)>\<circ\><around*|(|g\<circ\>f|)>>|<cell|=>|<cell|f<rsup|-1>\<circ\><around*|(|g<rsup|-1>\<circ\>g|)>\<circ\>f>>|<row|<cell|>|<cell|=>|<cell|f<rsup|-1>\<circ\>1<rsub|B>\<circ\>f>>|<row|<cell|>|<cell|=>|<cell|f<rsup|-1>\<circ\>f>>|<row|<cell|>|<cell|=>|<cell|1<rsub|A>>>>>
      </eqnarray*>

      so it is indeed a retraction.

      <\eqnarray*>
        <tformat|<table|<row|<cell|<around*|(|g\<circ\>f|)>\<circ\><around*|(|f<rsup|-1>\<circ\>g<rsup|-1>|)>>|<cell|=>|<cell|g\<circ\><around*|(|f\<circ\>f<rsup|-1>|)>\<circ\>g<rsup|-1>>>|<row|<cell|>|<cell|=>|<cell|g\<circ\>1<rsub|B>\<circ\>g<rsup|-1>>>|<row|<cell|>|<cell|=>|<cell|g\<circ\>g<rsup|-1>>>|<row|<cell|>|<cell|=>|<cell|1<rsub|C>>>>>
      </eqnarray*>

      so it is indeed a section.
    </proof>
  </proposition*>

  <subsection*|Exercise 11>

  <\itemize>
    <item>Let <math|f Fatima=coffee>, <math|f Omer=tea>, and <math|f
    Alysia=cocoa>.

    <item>No. \ Suppose <math|g\<of\>A\<rightarrow\>C> is an isomorphism.
    \ But <math|g> can't be both injective and surjective.
  </itemize>

  <subsection*|Exercise 12>

  <math|3!=6>

  <section*|Session 4>

  <subsection*|Exercise 1>

  We need to show that <math|h\<circ\>d=1<rsub|<around*|(|\<bbb-R\>,+|)>>>
  and <math|d\<circ\>h=1<rsub|<around*|(|\<bbb-R\>,+|)>>>, that is,
  <math|\<forall\>x\<in\><around*|(|\<bbb-R\>,+|)>\<nocomma\>,<around*|(|h\<circ\>d|)><around*|(|x|)>=x>
  and <math|\<forall\>x\<in\><around*|(|\<bbb-R\>,+|)>,<around*|(|d\<circ\>h|)><around*|(|x|)>=x>.
  \ For the first proposition,

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|(|h\<circ\>d|)><around*|(|x|)>>|<cell|=>|<cell|h<around*|(|d<around*|(|x|)>|)>>>|<row|<cell|>|<cell|=>|<cell|h<around*|(|2*x|)>>>|<row|<cell|>|<cell|=>|<cell|<frac|1|2>\<cdot\>2*x>>|<row|<cell|>|<cell|=>|<cell|x>>>>
  </eqnarray*>

  and for the second,

  <\eqnarray*>
    <tformat|<table|<row|<cell|<around*|(|d\<circ\>h|)><around*|(|x|)>>|<cell|=>|<cell|d<around*|(|h<around*|(|x|)>|)>>>|<row|<cell|>|<cell|=>|<cell|d<around*|(|<frac|1|2>*x|)>>>|<row|<cell|>|<cell|=>|<cell|2\<cdot\><frac|1|2>*x>>|<row|<cell|>|<cell|=>|<cell|x>>>>
  </eqnarray*>

  as required.

  <subsection*|Exercise 2>

  Let <math|f<around*|(|odd|)>=negative> and
  <math|f<around*|(|even|)>=positive>. \ We claim that
  <math|g\<of\><around*|(|<around*|{|positive,negative|}>,\<times\>|)>\<rightarrow\><around*|(|<around*|{|odd,even|}>,+|)>>
  such that <math|g<around*|(|negative|)>=odd> and
  <math|g<around*|(|positive|)>=even> is the inverse of <math|f> and that
  both are maps in our category.

  It is easy to see that <math|f\<circ\>g=1<rsub|<around*|(|<around*|{|positive,negative|}>,\<times\>|)>>>
  and <math|g\<circ\>f=1<rsub|<around*|(|<around*|{|even,odd|}>,+|)>>>. \ We
  show that <math|f> and <math|g> `respect the combining rules.'

  First, by cases, <math|\<forall\>x,y\<in\><around*|(|<around*|{|odd,even|}>,+|)>,f<around*|(|x+y|)>=f<around*|(|x|)>\<times\>f<around*|(|y|)>>:

  <\itemize>
    <item><math|f<around*|(|odd+odd|)>=f<around*|(|even|)>=positive=negative\<times\>negative=f<around*|(|odd|)>\<times\>f<around*|(|odd|)>>

    <item><math|f<around*|(|odd+even|)>=f<around*|(|odd|)>=negative=negative\<times\>positive=f<around*|(|odd|)>\<times\>f<around*|(|even|)>>

    <item><math|f<around*|(|even+odd|)>=f<around*|(|odd|)>=negative=positive\<times\>negative=f<around*|(|even|)>\<times\>f<around*|(|odd|)>>

    <item><math|f<around*|(|even+even|)>=f<around*|(|even|)>=positive=positive\<times\>positive=f<around*|(|even|)>\<times\>f<around*|(|even|)>>
  </itemize>

  Again, by cases, <math|\<forall\>x,y\<in\><around*|(|<around*|{|positive,negative|}>,\<times\>|)>,g<around*|(|x\<times\>y|)>=g<around*|(|x|)>+g<around*|(|y|)>>:

  <\itemize>
    <item><math|g<around*|(|positive\<times\>positive|)>=g<around*|(|positive|)>=even=even+even=f<around*|(|positive|)>+f<around*|(|positive|)>>

    <item><math|g<around*|(|positive\<times\>negative|)>=g<around*|(|negative|)>=odd=even+odd=g<around*|(|positive|)>+g<around*|(|negative|)>>

    <item><math|g<around*|(|negative\<times\>positive|)>=g<around*|(|negative|)>=odd=odd+even=g<around*|(|negative|)>+g<around*|(|positive|)>>

    <item><math|g<around*|(|negative\<times\>negative|)>=g<around*|(|positive|)>=even=odd+odd=g<around*|(|negative|)>+g<around*|(|negative|)>>
  </itemize>

  as required.

  <subsection*|Exercise 3>

  <\enumerate-alpha>
    <item>Impostor! \ <math|<around*|(|x+y|)>+1\<neq\><around*|(|x+1|)>+<around*|(|y+1|)>>

    <item>Impostor! \ <math|sq> is not an isomorphism because it is not
    injective

    <item>Impostor! \ as in (b)

    <item>Ok. \ Is its own inverse. \ <math|-<around*|(|x+y|)>=<around*|(|-x|)>+<around*|(|-y|)>>

    <item>Impostor! \ <math|-<around*|(|x\<times\>y|)>\<neq\><around*|(|-x|)>\<times\><around*|(|-y|)>>

    <item>Impostor! \ Bad codomain.
  </enumerate-alpha>

  <section*|Session 5>

  <subsection*|Exercise 1>

  <subsubsection*|(a)>

  <\proposition*>
    <\math>
      \<forall\>f\<of\>A\<rightarrow\>B,\<forall\>h\<of\>A\<rightarrow\>C,

      <around*|(|\<exists\>g\<of\>B\<rightarrow\>C,h=g\<circ\>f|)>\<rightarrow\><around*|(|\<forall\>a<rsub|1>
      a<rsub|2>\<of\>\<b-1\>\<rightarrow\>A,f a<rsub|1>=f
      a<rsub|2>\<rightarrow\>h a<rsub|1>=h a<rsub|2>|)>
    </math>

    <\proof>
      <math|f a<rsub|1>=f a<rsub|2>\<Rightarrow\><around*|(|g\<circ\>f|)>
      a<rsub|1>=<around*|(|g\<circ\>f|)> a<rsub|2>\<Rightarrow\>h a<rsub|1>=h
      a<rsub|2>>

      \;
    </proof>
  </proposition*>

  <subsubsection*|(b)>

  <\proposition*>
    <\math>
      \<forall\>f\<of\>A\<rightarrow\>B,\<forall\>h\<of\>A\<rightarrow\>C

      <around*|(|\<forall\>a<rsub|1> a<rsub|2>\<of\>\<b-1\>\<rightarrow\>A,f\<circ\>a<rsub|1>=f\<circ\>a<rsub|2>\<rightarrow\>h\<circ\>a<rsub|1>=h\<circ\>a<rsub|2>|)>\<Rightarrow\><around*|(|\<exists\>g\<of\>B\<rightarrow\>C,h=g\<circ\>f|)>
    </math>

    <\proof>
      Consider the subsets <math|B<rprime|'>=<around*|{|b\<in\>B<mid|\|>\<exists\>a\<in\>\<b-1\>\<rightarrow\>A,f\<circ\>a=b|}>>
      and <math|C<rprime|'>> with the analogous definition. \ These sets have
      the same cardinality, by the assumptions on <math|f> and <math|h>.
      \ There is therefore an isomorphism <math|g<rprime|'>> between them.
      \ We may freely add elements to <math|B<rprime|'>> and
      <math|C<rprime|'>> to get <math|B> and <math|C>, and extend
      <math|g<rprime|'>> in any manner to get <math|g>.
    </proof>
  </proposition*>

  <subsection*|Exercise 2>

  <subsubsection*|(a)>

  <\proposition*>
    <\math>
      \<forall\>g\<of\>B\<rightarrow\>C,\<forall\>h\<of\>A\<rightarrow\>C,

      <around*|(|\<exists\>f\<of\>A\<rightarrow\>B,g\<circ\>f=h|)>\<rightarrow\><around*|(|\<forall\>a\<in\>A,\<exists\>b\<in\>B,h<around*|(|a|)>=g<around*|(|b|)>|)>
    </math>

    <\proof>
      Let <math|a\<in\>A>. \ Take <math|b=f<around*|(|a|)>>. \ Then
      <math|h<around*|(|a|)>=<around*|(|g\<circ\>f|)><around*|(|a|)>=g<around*|(|f<around*|(|a|)>|)>=g<around*|(|b|)>>.
    </proof>
  </proposition*>

  <subsubsection*|(b)>

  <\proposition*>
    <\math>
      \<forall\>g\<of\>B\<rightarrow\>C,\<forall\>h\<of\>A\<rightarrow\>C,

      <around*|(|\<forall\>a\<in\>A,\<exists\>b\<in\>B,h<around*|(|a|)>=g<around*|(|b|)>|)>\<rightarrow\><around*|(|\<exists\>f\<of\>A\<rightarrow\>B,g\<circ\>f=h|)>
    </math>

    <\proof>
      For each <math|a>, let <math|f> `choose' the <math|b> such that
      <math|g<around*|(|b|)>=h<around*|(|a|)>>.
    </proof>
  </proposition*>

  <subsection*|Exercise 3>

  There are <math|8> internal diagrams, drawn in the obvious way.

  <section*|Session 6>

  (no exercises)

  <section*|Session 7>

  (no exercises)

  <section*|Session 8>

  (no exercises)

  <section*|Session 9>

  <subsection*|Exercise 1>

  <\proposition*>
    Unless the set <math|A> has a point and <math|B> has none, then there is
    at least one map from <math|A> to <math|B>.

    <\proof>
      Suppose it is not the case that <math|A> has a point and <math|B> has
      none. \ First, consider that <math|A> has no point. \ Then <math|A> is
      empty, so there is exactly one map from <math|A> to <math|B>. \ Next,
      consider that <math|B> has at least one point. \ Then <math|B> is
      non-empty, so there is at least one map from <math|A> to <math|B>.
    </proof>
  </proposition*>

  <subsection*|Exercise 2>

  <\description>
    <item*|R>We must show that there are maps
    <math|A<above|\<longrightarrow\>|s>A<above|\<longrightarrow\>|r>A> st
    <math|r*s=1<rsub|A>>. \ Just take <math|s=r=1<rsub|A>>.

    <item*|T>Suppose <math|A<above|\<longrightarrow\>|s>B<above|\<longrightarrow\>|r>A>
    and <math|r*s=1<rsub|A>> and <math|B<above|\<longrightarrow\>|s<rprime|'>>C<above|\<longrightarrow\>|r<rprime|'>>B>
    and <math|r<rprime|'>*s<rprime|'>=1<rsub|B>>. \ Then
    <math|A<above|\<longrightarrow\>|s<rprime|'>*s>C<above|\<longrightarrow\>|r<rprime|'>*r>A>
    and <math|r*r<rprime|'>*s<rprime|'>*s=r*s=1<rsub|A>>.
  </description>

  <subsection*|Exercise 3>

  Take <math|f=r<rprime|'>*s> and let <math|g=r*s<rprime|'>>. \ Then
  <math|g*f=r*s<rprime|'>*r<rprime|'>*s=r*e*s=r*s*r*s=1<rsub|A>*1<rsub|A>=1<rsub|A>>,
  and <math|f*g=r<rprime|'>*s*r*s<rprime|'>=r<rprime|'>*e*s<rprime|'>=r<rprime|'>*s<rprime|'>*r<rprime|'>*s<rprime|'>=1<rsub|A>*1<rsub|A>=1<rsub|A>>.
  \ Therefore <math|f> is an isomorphism.

  <section*|Quiz>

  <section*|How to solve the quiz problems>

  <section*|Composition of opposed maps>

  <section*|Summary/quiz on pairs of `opposed' maps>

  <section*|Summary: On the equation <math|p\<circ\>j\<equallim\>1<rsub|A>>>

  <section*|Review of `I-words'>

  <section*|Test 1>

  <section*|Session 10>

  \;
</body>

<\initial>
  <\collection>
    <associate|info-flag|none>
    <associate|preamble|false>
  </collection>
</initial>

<\references>
  <\collection>
    <associate|auto-1|<tuple|?|1>>
    <associate|auto-10|<tuple|<with|mode|<quote|math>|\<bullet\>>|2>>
    <associate|auto-11|<tuple|<with|mode|<quote|math>|\<bullet\>>|2>>
    <associate|auto-12|<tuple|<with|mode|<quote|math>|\<bullet\>>|2>>
    <associate|auto-13|<tuple|<with|mode|<quote|math>|\<bullet\>>|2>>
    <associate|auto-14|<tuple|<with|mode|<quote|math>|\<bullet\>>|3>>
    <associate|auto-15|<tuple|<with|mode|<quote|math>|\<bullet\>>|3>>
    <associate|auto-16|<tuple|<with|mode|<quote|math>|\<bullet\>>|3>>
    <associate|auto-17|<tuple|c|3>>
    <associate|auto-18|<tuple|c|3>>
    <associate|auto-19|<tuple|c|3>>
    <associate|auto-2|<tuple|?|1>>
    <associate|auto-20|<tuple|T|4>>
    <associate|auto-21|<tuple|T|5>>
    <associate|auto-22|<tuple|c|5>>
    <associate|auto-23|<tuple|5|6>>
    <associate|auto-24|<tuple|5|6>>
    <associate|auto-25|<tuple|5|7>>
    <associate|auto-26|<tuple|5|7>>
    <associate|auto-27|<tuple|5|8>>
    <associate|auto-28|<tuple|5|9>>
    <associate|auto-29|<tuple|5|11>>
    <associate|auto-3|<tuple|<with|mode|<quote|math>|\<bullet\>>|1>>
    <associate|auto-30|<tuple|5|12>>
    <associate|auto-31|<tuple|<with|mode|<quote|math>|\<bullet\>>|12>>
    <associate|auto-32|<tuple|<with|mode|<quote|math>|\<bullet\>>|12>>
    <associate|auto-33|<tuple|<with|mode|<quote|math>|\<bullet\>>|12>>
    <associate|auto-34|<tuple|<with|mode|<quote|math>|\<bullet\>>|?>>
    <associate|auto-35|<tuple|<with|mode|<quote|math>|\<bullet\>>|?>>
    <associate|auto-36|<tuple|f|?>>
    <associate|auto-37|<tuple|f|?>>
    <associate|auto-38|<tuple|f|?>>
    <associate|auto-39|<tuple|f|?>>
    <associate|auto-4|<tuple|<with|mode|<quote|math>|\<bullet\>>|1>>
    <associate|auto-40|<tuple|f|?>>
    <associate|auto-41|<tuple|f|?>>
    <associate|auto-42|<tuple|f|?>>
    <associate|auto-43|<tuple|f|?>>
    <associate|auto-44|<tuple|f|?>>
    <associate|auto-45|<tuple|f|?>>
    <associate|auto-46|<tuple|f|?>>
    <associate|auto-47|<tuple|f|?>>
    <associate|auto-48|<tuple|f|?>>
    <associate|auto-49|<tuple|f|?>>
    <associate|auto-5|<tuple|<with|mode|<quote|math>|\<bullet\>>|1>>
    <associate|auto-50|<tuple|T|?>>
    <associate|auto-51|<tuple|T|?>>
    <associate|auto-52|<tuple|T|?>>
    <associate|auto-53|<tuple|T|?>>
    <associate|auto-54|<tuple|T|?>>
    <associate|auto-55|<tuple|T|?>>
    <associate|auto-56|<tuple|T|?>>
    <associate|auto-57|<tuple|T|?>>
    <associate|auto-58|<tuple|T|?>>
    <associate|auto-6|<tuple|<with|mode|<quote|math>|\<bullet\>>|1>>
    <associate|auto-7|<tuple|<with|mode|<quote|math>|\<bullet\>>|1>>
    <associate|auto-8|<tuple|<with|mode|<quote|math>|\<bullet\>>|2>>
    <associate|auto-9|<tuple|<with|mode|<quote|math>|\<bullet\>>|2>>
  </collection>
</references>

<\auxiliary>
  <\collection>
    <\associate|toc>
      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Session
      1> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-1><vspace|0.5fn>

      <with|par-left|<quote|1tab>|Exercise 1
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-2>>

      <with|par-left|<quote|1tab>|Exercise 2
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-3>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Article
      I> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-4><vspace|0.5fn>

      <with|par-left|<quote|1tab>|Exercise 1
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-5>>

      <with|par-left|<quote|1tab>|Exercise 2
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-6>>

      <with|par-left|<quote|1tab>|Exercise 3
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-7>>

      <with|par-left|<quote|1tab>|Exercise 4
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-8>>

      <with|par-left|<quote|1tab>|Exercise 5
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-9>>

      <with|par-left|<quote|1tab>|Exercise 6
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-10>>

      <with|par-left|<quote|1tab>|Exercise 7
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-11>>

      <with|par-left|<quote|1tab>|Exercise 8
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-12>>

      <with|par-left|<quote|1tab>|Exercise 9
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-13>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Session
      2> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-14><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Session
      3> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-15><vspace|0.5fn>

      <with|par-left|<quote|1tab>|Exercise 1
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-16>>

      <with|par-left|<quote|1tab>|Exercise 2
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-17>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Article
      II> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-18><vspace|0.5fn>

      <with|par-left|<quote|1tab>|Exercise 1
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-19>>

      <with|par-left|<quote|1tab>|Exercise 2
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-20>>

      <with|par-left|<quote|1tab>|Exercise 3
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-21>>

      <with|par-left|<quote|1tab>|Exercise 4
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-22>>

      <with|par-left|<quote|1tab>|Exercise 5
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-23>>

      <with|par-left|<quote|1tab>|Pick's Formula
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-24>>

      <with|par-left|<quote|1tab>|Exercise 6
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-25>>

      <with|par-left|<quote|1tab>|Exercise 7
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-26>>

      <with|par-left|<quote|1tab>|Exercise 8
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-27>>

      <with|par-left|<quote|1tab>|Exercise 9
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-28>>

      <with|par-left|<quote|1tab>|Exercise 10
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-29>>

      <with|par-left|<quote|1tab>|Exercise 11
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-30>>

      <with|par-left|<quote|1tab>|Exercise 12
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-31>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Session
      4> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-32><vspace|0.5fn>

      <with|par-left|<quote|1tab>|Exercise 1
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-33>>

      <with|par-left|<quote|1tab>|Exercise 2
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-34>>

      <with|par-left|<quote|1tab>|Exercise 3
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-35>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Session
      5> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-36><vspace|0.5fn>

      <with|par-left|<quote|1tab>|Exercise 1
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-37>>

      <with|par-left|<quote|2tab>|(a) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-38>>

      <with|par-left|<quote|2tab>|(b) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-39>>

      <with|par-left|<quote|1tab>|Exercise 2
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-40>>

      <with|par-left|<quote|2tab>|(a) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-41>>

      <with|par-left|<quote|2tab>|(b) <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-42>>

      <with|par-left|<quote|1tab>|Exercise 3
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-43>>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Session
      6> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-44><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Session
      7> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-45><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Session
      8> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-46><vspace|0.5fn>

      <vspace*|1fn><with|font-series|<quote|bold>|math-font-series|<quote|bold>|Session
      9> <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-47><vspace|0.5fn>

      <with|par-left|<quote|1tab>|Exercise 1
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-48>>

      <with|par-left|<quote|1tab>|Exercise 2
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-49>>

      <with|par-left|<quote|1tab>|Exercise 3
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-50>>

      <with|par-left|<quote|1tab>|Exercise 4
      <datoms|<macro|x|<repeat|<arg|x>|<with|font-series|medium|<with|font-size|1|<space|0.2fn>.<space|0.2fn>>>>>|<htab|5mm>>
      <no-break><pageref|auto-51>>
    </associate>
  </collection>
</auxiliary>