\documentclass[dvipsnames, fleqn]{jfp}
\usepackage{url}
\let\Bbbk\relax  % avoiding error "Bbbk' already defined."
\usepackage{tikz}
\usepackage{chngcntr} % for \counterwithout
\usepackage{caption}
\usepackage{subcaption}
\usepackage{scalerel}

%% lhs2TeX monadic-opt.lhs | pdflatex --jobname=monadic-opt

%if False
\begin{code}
import Prelude hiding (repeat)
(===) :: a -> a -> a
(===) = undefined

infixr 0 ===
\end{code}
%endif

%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include exists.fmt

%include Formatting.fmt
%include Relation.fmt


%%\email{scm@iis.sinica.edu.tw}

\usepackage{doubleequals}

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}

\def\commentbegin{\quad$\{$~}
\def\commentend{$\}$}
\mathindent=\parindent
\addtolength{\mathindent}{0.3cm}
\allowdisplaybreaks

\newcommand{\tagx}[1][]{\refstepcounter{equation}(\theequation)\label{#1}}
\newcommand\numberthis{\refstepcounter{equation}\tag{\theequation}}

\newcommand{\todo}[1]{{\color{brown}\lbrack{\bf to do}: #1 \rbrack}}

\counterwithout{equation}{section}

%format b0
%format b1
%format y0
%format y1
%format z0
%format z1
%format z2
%format Set1


\begin{document}

\righttitle{A Monadic Notation for Calculating Optimisation Algorithms}
\lefttitle{S-C. Mu}

\title{A Monadic Notation for Calculating Optimisation Algorithms}
\begin{authgrp}
\author{Shin-Cheng Mu}
\affiliation{Institute of Information Science, Academia Sinica, Taipei, Taiwan}
\author{You-Zheng Yu}
\affiliation{National Taiwan University, Taipei, Taiwan}
\end{authgrp}

\date{}
\journaltitle{JFP}
\cpr{Cambridge University Press}
\doival{yyyy/xxxxx}
\jnlDoiYr{2025}

\begin{abstract}

\end{abstract}

\maketitle

\section{Introduction}

Program calculation is the technique of constructing a program from a specification in a stepwise manner, where each step is justified by established properties.
A canonical example of functional program derivation is the \emph{maximum segment sum} problem: given a list of numbers, compute the largest possible sum of a consecutive segment.
The problem can be specified by:
\begin{spec}
  mss :: List Int -> Int
  mss = maximum . map sum . segments {-"~~,"-}
\end{spec}
where |segments :: List a -> List (List a)| computes all consecutive segments of a given list. The sums of each segment are computed, before |maximum :: List Int -> Int| returns the largest integer.
The one-liner specification above, if executed, is rather inefficient.
However, within several lines of reasoning, one may transform it to a program consisting of a |foldr| before a |maximum|, both run in time linear to the length of the input:
\begin{spec}
   maximum . map sum . segments
=    {- |segments| can be defined as |map inits . tails| -}
   maximum . map sum . map inits . tails
=    {- ... other steps omitted ... -}
   maximum . foldr (\x y -> (x + y) `max` 0) 0 {-"~~."-}
\end{spec}
The specification |mss| is a total function --- for each input it computes exactly one maximum sum.
The final program and the specification are related by equality,
which means that, for all input, the final program must yield exactly the same one result which |mss| would compute.

Pedagogical examples of program calculation for such optimisation problems tend to return the optimal value (in this case, the sum), rather than the solution that yields the optimal value (the list),
because this approach would not be feasible otherwise.
When there are multiple solutions that yield the optimal value.
The specification, being a function, has to pick a particular one, which the implementation has to return.
In the construction of a sorting algorithm, for example,
having to decide, in the specification phase, what list to return when there are items having the same key would severely limit the algorithm one can derive (e.g., limiting one to construct stable sorting), if not making the specification impossible at all (it is hard to predict how, say, quicksort arranges items having the same keys).
One therefore needs a different framework, where a specification describes a collection of solution that is allowed by the final program, which no longer equals, but is instead contained by the specification.

One of the possibilities is to use relations as specifications.
Foundations of this approach were laid by works including \cite{BackhousedeBruin:91:Relational}, \cite{Aarts:92:Relational}, \cite{BackhouseHoogendijk:92:Elements}, etc,
before \cite{BirddeMoor:97:Algebra}, taking a more abstract, categorical approach,
presented general theories for constructing various forms of greedy, thinning, and dynamic programming algorithms.
\cite{BirddeMoor:97:Algebra} presented a point-free calculus that is concise, elegant, and surprisingly expressive.
\todo{Why AoP is amazing}
Such conciseness and expressiveness also turned out to be a curse, however.
For those who not sharing the background, the calculus has a sharp learning curve, which limited its popularity to a small circle of enthusiasts.
\todo{Why AoP can't be popular.}

Efforts has been made to re-introduce variables back to the relational calculus, for example, \cite{deMoorGibbons:00:Pointwise}.
One cannot help feeling unease with some of its peculiarities, for example
\todo{What?}
Around two decades later, \cite{BirdRabe:19:How} presented a theoretical background of ``multifunctions'',
which was then used in
\cite{BirdGibbons:20:Algorithm}.
\todo{What is wrong with it?}

\todo{Why we recommend using monads.}

\paragraph*{In this article} we consider problems having the form:
\begin{spec}
  min . (filt p <=< foldR f e) {-"~~."-}
\end{spec}
where |(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)| is Kliseli composition and |(.)| is ordinary function composition.
Given an input of type |List A|, the collection of all solution candidates is generated by |foldR f e :: List A -> M B|, a monadic variation of fold on lists.
The function |filt :: (b -> Bool) -> b -> M b| keeps those satisfies predicate |p|, and |min :: M b -> M b| keeps only those having minimum value under some chosen ordering.
We then discuss conditions under which the specification can be refined to a fold-based greedy algorithm --- one where we greedily keep only the locally best solution in each step of the fold,
or a \emph{thinning} algorithm, where in each step of the fold we keep a set of solution candidates that still might be useful.

All these were covered in \cite{BirddeMoor:97:Algebra}.
Rather than solving new problems or discovering new algorithms, the purpose of this article is to propose new notations that make previous derivations more accessible and accurate, while not being too cumbersome.
In traditional functional programming, one may reason about a functional program by induction on the input.
This article aims to show that reasoning about monadic programs is just like that: one only need to make use of monad laws and properties of effect operators.
\todo{Say more, and polish.}

\section{Preliminaries}

We introduce in this section the building blocks we need.

\subsection{Nondeterminism Monad}

A monad consists of a type constructor |M| and operators |return :: a -> M a| and |(>>=) :: M a -> (a -> M b) -> M b| that satisfy the \emph{monad laws}:
\begin{align*}
& \mbox{{\bf right identity}:} & |m >>= return| &= |m|  \mbox{~~,}\\
& \mbox{{\bf left identity}:}  & |return x >>= f| &= |f x| \mbox{~~,}\\
& \mbox{{\bf associativity}:}  &|(m >>= f) >>= g| &= |m >>= (\x -> f x >>= g)| \mbox{~~.}
\end{align*}
The operator |(>>) :: M a -> M b -> M b|, defined by |m >> n = m >>= (\_ -> n)|, ignores the result of |m| before executing |n|.
A function |a -> b| can be lifted to monad |M| by |fmap|:
\begin{spec}
fmap :: (a -> b) -> M a -> M b
fmap f m = m >>= (return . f) {-"~~."-}
\end{spec}
We also write |fmap f m| infix as |f <$> m|, where the operator |(<$>)| is left-associative like function application.
It follows easily from the monad laws that
|id <$> m = m| and |(f . g) <$> m = f <$> (g <$> m)|, that is, |M| is a functor with |(<$>)| as its functorial map.

In this paper we will also make extensive use of the reverse bind and the Kliseli composition:
\begin{spec}
(=<<) :: (a -> M b) -> M a -> M b
f =<< m = m >>= f {-"~~,"-}

(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)
(f <=< g) x = f =<< g x {-"~~."-}
\end{spec}
Kliseli composition |(<=<)| is associative, |(=<<)| is right-associative, and both bind looser than function composition |(.)|.
We will add parentheses where there might be confusion.

Alternatively, a monad can be defined by three operators: |return :: a -> M a|, |join :: M (M a) -> M a|, and its functorial map |(<$>) :: (a -> b) -> M a -> M b|. The two styles of definitions are equivalent, as |(>>=)| can be defined in terms of |join| and |(<$>)|, and vice versa:
\begin{spec}
join :: M (M a) -> M a
join m = m >>= id {-"~~,"-}

(>>=) :: M a -> (a -> M b) -> M b
m >>= f = join (f <$> m) {-"~~."-}
\end{spec}

Non-determinism is the only effect we are concerned with in this article: |M a| denotes a nondeterministic computation that may yield zero, one, or more values of type |a|.
We let |mplus :: M a -> M a -> M a| denote nondeterministic choice and |mzero :: M a| failure. Together they form a monoid (that is, |mplus| is associative with |mzero| as its identity element) and satisfy the following laws:
\begin{align*}
  |mzero >>= f| &= |mzero| \mbox{~~,}\\
  |f >> mzero|  &= |mzero| \mbox{~~,}\\
  |m >>= (\x -> f x `mplus` g x)| &= |(m >>= f) `mplus` (m >>= g)| \mbox{~~,}\\
  |(m `mplus` n) >>= f| &= |(m >>= f) `mplus` (n >>= f)| \mbox{~~.}
\end{align*}
Furthermore, |mplus| is commutative (|m `mplus` n = n `mplus` m|) and idempotent (|m `mplus` m = m|).

The containment relation of non-determinism monad is defined by:
\begin{spec}
m `sse` n = (m `mplus` n = n) {-"~~."-}
\end{spec}
When |m `sse` n|, we say that |m| refines |n|.
Every value |m| might yield is a value allowed by |n|.
We also lift the relation to functions: |f `sse` g = (forall x : f x `sse` g x)|.

A structure that supports all the operations above is the set monad: for all type |a|,
|m :: P a| is a set whose elements are of type |a|,
|mzero| is the empty set, |mplus| is set union for two sets, |join| is union for a set of sets, |(`sse`)| is set inclusion, |return| forms a singleton set, and |m >>= f| is given by |join {f x || x <- m }|.
For the rest of the paper we take |M = P|.

The set |any : P a| contains all elements having type |a|.
Computationally, it creates an arbitrary element of its type.
The command |filt : (a -> Bool) -> a -> P a| is defined by
\begin{spec}
filt p x  | p x        = return x
          | otherwise  = fail {-"~~."-}
\end{spec}
It returns its input |x| if it satisfies |p|, and fails otherwise.%
\footnote{Conventionally there is a function |guard :: Bool -> M ()| that returns |()| when the input is true, and |filt p x| is defined by |do { guard (p x); return x }|. In this paper we try to introduce less construct and use only |filt|.}

\subsection{An Agda Model of Set Monad}

To ensure that there is indeed a model of our set monad, we built one in Agda.
A first attempt was to represent a set |P| by its characteristic predicate:
\begin{spec}
P : Set -> Set1
P a = a -> Set {-"~~."-}
\end{spec}
Given |x : a|, |P x| is a type, or a proposition, stating the conditions under which |x| is in the set denoted by |P x|.
Monad operators |return| and |(>>=)| are defined by
\begin{spec}
return : {a : Set} -> a -> P a
return x  = \y ->  x <=> y {-"~~,"-}
(>>=) : {a b : Set} -> P a -> (a -> P b) -> P b
m >>= f   = \y -> Sum{-"\!"-}[x `mem` a] (m x * f x y) {-"~~,"-}
\end{spec}
where |(<=>)| is propositional equality, and |Sum| denotes dependent pair.
That is, |y| is a member of the set |return x| exactly when |x <=> y|,
and |y| is a member of |m >>= f| if there exists a witness |x|, presented in the dependent pair, that is a member of the set |m|, and |y| is a member of the set |f x|.

We would soon get stuck when we try to prove any of its properties.
To prove the right identity law |m >>= return = m|, for example, amounts to proving that
\begin{spec}
  (\y -> Sum{-"\!"-}[x `mem` a] (m x * x <=> y)) {-"~"-}<=>{-"~"-} m {-"~~."-}
\end{spec}
The righthand side |m| is a function which yields, for each member |y|, a proof that |y| is in |m|,
while the lefthand side is a function which produces, for each member |y|, a dependent pair consisting of a value |x : a| , a proof that |x| is in |m|, and a proof that |x <=> y|.
While logically we recognize that they are equivalent, in the type theory of Agda the two sides are different, albeit isomorphic, types.

\todo{Cubical Agda}

\subsection{Monadic Fold}

We define the monadic fold on lists as:
\begin{spec}
foldR :: (a -> b -> P b) -> P b -> List a -> P b
foldR f e []      = e
foldR f e (x:xs)  = f x =<< foldR f e xs {-"~~."-}
\end{spec}
Given |h :: List a -> P b|, the \emph{fixed-point properties}, that is, sufficient conditions for |h| to contain or be contained by |foldR f e| are given by:
\begin{align}
|foldR f e `sse` h| & |{-"~"-}<=={-"~"-} e `sse` h [] {-"\,"-}&&{-"\,"-} f x =<< h xs `sse` h (x:xs)  {-"~~,"-}| \label{eq:foldR-comp} \\
|h `sse` foldR f e| & |{-"~"-}<=={-"~"-} h [] `sse` e {-"\,"-}&&{-"\,"-} h (x:xs) `sse` f x =<< h xs  {-"~~."-}|
\end{align}
The properties above can be proved by routine induction on the input list.
One may then prove the following |foldR| fusion rule:
\begin{equation}
  |foldR g (h e) `sse` h . foldR f e {-"~"-}<=={-"~"-} g x =<< h m `sse` h (f x =<< m) {-"~~."-}|
\end{equation}

%format f0
%format f1
%format e0
%format e1
With \eqref{eq:foldR-comp} it is easy to show that |foldR| is monotonic:
\begin{equation}
|foldR f0 e0 `sse` foldR f1 e1 {-"~"-}<=={-"~"-} f0 `sse` f1 && e0 `sse` e1  {-"~~."-}|
\label{eq:foldR-monotonicity}
\end{equation}
Note that in |f0 `sse` f1|, set inclusion is lifted to denote |f0 x y `sse` f1 x y| for all |x| and |y|.

Finally, monadic |foldR| can be refined to pure |foldr| if both of its arguments are pure:
\begin{equation}
|return (foldr f e) = foldR (\x -> return . f x) (return e) {-"~~."-}|
\label{eq:foldr-foldR}
\end{equation}

\subsection{Minimum}

Consider a binary relation |unlhd| on some type |a|.
A value |x :: a| is a minimum of |xs :: P a| if |x| is in |xs|, and for every element |y `elem` xs| we have |x `unlhd` y|.
The definition itself does not assume much from |unlhd|.
In particular, since |unlhd| is not unnecessarily anti-symmetric, minimum elements might not be unique.
The function |min_unlhd :: P a -> P a| takes a set and returns a refined set that keeps all the minimum elements and nothing else.
In set-theoretical notation, |min_unlhd| can be defined by the following equivalence:
for all |xs| and |ys|,
\begin{equation}
|ys `sse` min_unlhd xs {-"~"-}<==>{-"~"-} ys `sse` xs && (forall y `mem` ys : (forall x `mem` xs : y `unlhd` x)) {-"~~."-}|
\label{eq:min-def-set}
\end{equation}
We omit the subscript |unlhd| when it is clear from the context or not relevant.
Letting |ys = min xs|, the |(==>)| direction of \eqref{eq:min-def-set} says that |min xs| is a subset of |xs|, and every member in |min xs| is no greater than any member in |xs|. The |(<==)| direction says that |min xs| is the largest such set --- any |ys| satisfying the righthand side is a subset of |min xs|.

In calculation, we often want to refine expressions of the form |min . f| where |f| generates a set. Therefore the following \emph{universal property} of |min| is more useful: for all |h| and |f| of type |a -> P b|,
\begin{equation}
|h `sse` min_unlhd . f {-"~"-}<==>{-"~"-} h `sse` f && (forall x : (forall y0 `mem` h x : (forall y1 `mem` f x : y0 `unlhd` y1))) {-"~~."-}|
\label{eq:min-univ-set}
\end{equation}
Properties \eqref{eq:min-def-set} and \eqref{eq:min-univ-set} are equivalent.
\todo{argue for that}

The aim of our work, however, is to capture the ideas above in a monadic notation, such that programs can be manipulated and reasoned about in the monadic language.
It turns out that \eqref{eq:min-univ-set} can be rewritten monadically as below:
%\begin{spec}
%X `sse` min_R . f {-"\,"-}<=> {-"\,"-}  X `sse` f &&
%                                        (  do  a   <- any
%                                               b0  <- X a
%                                               b1  <- f a
%                                               return (b0, b1) {-"\,"-} `sse`
%                                                 do  (b0, b1) <- any
%                                                     filt R (b0, b1) {-"\,"-}) {-"~~."-}
%\end{spec}
\begin{equation}
|h `sse` min_unlhd . f|\mbox{~~}|<==>|\mbox{~~} |h `sse` f &&|~
\setlength{\jot}{-1pt}
\left(
 \begin{aligned}
 |do|~ & |x <- any| \\
       & |y0 <- h x| \\
       & |y1 <- f x| \\
       & |return (y0, y1)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(y0, y1) <- any| \\
       & |filt unlhd (y0, y1)|
 \end{aligned}
 \right)\mbox{~~.}
 \label{eq:min-univ-monadic}
\end{equation}
In \eqref{eq:min-univ-monadic} and from now on we abuse the notation a bit,
using |filt unlhd| to denote |filt (\(y,z) -> y `unlhd` z)|.
The large pair of parentheses in \eqref{eq:min-univ-monadic} relates two monadic values. On the lefthand side we non-deterministically generate a pair of values |y0| and |y1|, which are respectively a result of |h| and |f| for an arbitrary input |x|. The inclusion says that |(y0, y1)| must be contained by the monad on the righthand side, which contains all pairs |(y0, y1)| as long as |y0 `unlhd` y1|.

Letting |h = min . f| in \eqref{eq:min-univ-monadic}, we get the |min|-cancelation law:
\begin{equation}
\setlength{\jot}{-1pt}
 \begin{aligned}
 |do|~ & |x <- any| \\
       & |y0 <- min (f x)| \\
       & |y1 <- f x| \\
       & |return (y0, y1)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(y0, y1) <- any| \\
       & |filt unlhd (y0, y1)| \mbox{~~.}
 \end{aligned}
 \label{eq:min-cancelation}
\end{equation}

By defining the ``split'' operator |split f g x = do { y <- f x; z <- g x; return (y,z) }|,
\eqref{eq:min-univ-monadic} can be written more concisely as below:
\begin{equation*}
|h `sse` min_unlhd . f|\mbox{~~}|<==>|\mbox{~~} |h `sse` f &&|~
|split h f =<< any {-"\,"-}`sse`{-"\,"-} filt unlhd =<< any| \mbox{~~.}
\end{equation*}
We may then manipulate expressions using properties of the |split| operator.
The |min|-cancelation law is written as
|split (min_unlhd . f) f =<< any {-"\,"-}`sse`{-"\,"-} filt unlhd =<< any|.

Maximum is defined as the dual of minimum:
\begin{spec}
  max_unlhd = min_unrhd {-"~~."-}
\end{spec}

\paragraph*{Promotion into Kliseli Composition.}~
The function |min| promotes into |join|:
%if False
\begin{code}
-- propMinJoin :: forall {k} (a :: Type). P (P a) -> P a
propMinJoin xss = min (join xss) === min (join (fmap min xss))
\end{code}
%endif
\begin{equation}
  |min . join === min . join  . fmap min| \mbox{~~.}
   \label{eq:MinJoin}
\end{equation}
Consider an input |xss :: P (P a)|, a set of sets, as the input for both sides. On the lefthand side, |xss| is joined into a single set, from which we keep the minimums. It is equivalent to the righthand side, where we choose the minimums of each of the sets in |xss|, before keeping their minimums.
With \eqref{eq:MinJoin} and the definition of |(>>=)| by |join| we can show how |min| promotes into |(=<<)| or |(<=<)|:
\begin{equation}
  |min (f <=< g) === min ((min . f) <=< g)| \mbox{~~.}
   \label{eq:MinKComp}
\end{equation}
%The proof goes:
%%if False
%\begin{code}
%-- propMaxJoin :: forall {k} (a :: Type). P (P a) -> P a
%propMaxBind f g xs =
%\end{code}
%%endif
%\begin{code}
%      max (f =<< g xs)
% ===    {- definition of |(=<<)| -}
%      max (join (fmap f (g xs)))
% ===    {- \eqref{eq:MaxJoin} -}
%      max (join (fmap (max . f) (g xs)))
% ===    {- definition of |(=<<)| -}
%      max ((max . f) =<< g xs) {-"~~."-}
%\end{code}

\paragraph*{Conversion from Lists.}~
The function |member| non-deterministically returns an element of the given list.
Put it in another way, it converts a list to a set:
\begin{code}
member :: List a -> P a
member []        = mzero
member (x : xs)  = return x <|> member xs {-"~~."-}
\end{code}

Monadic |min| can be refined to operate on lists
\begin{equation}
 |return . minlist_unlhd`sse` min_unlhd . member | \label{eq:MaxMaxList}
\end{equation}
where |minlist| is some implementation of minimum on lists, e.g.
\begin{spec}
  minlist :: List a -> a
  minlist [x] = x
  minlist (x : y : xs) = x `bmin` minlist (y : ys) {-"~~,"-}
   where x `bmin` y  =if x `unlhd` y then x else y {-"~~."-}
\end{spec}

\paragraph*{In the Agda Model}
we implement |min| by:

\todo{more here.}

It is then proved in Agda that the above implementation satisfies \eqref{eq:min-univ-monadic}.

\section{The Greedy Theorem}

A function |f : b -> P b| is said to be \emph{monotonic on |unlhd|} if the following holds:
\begin{equation}
\setlength{\jot}{-1pt}
\begin{aligned}
|do|~ & |(y0, y1) <- any|\\
      & |z1 <- f y1| \\
      & |filt unlhd (y0, y1)|\\
      & |return (y0, z1)|
\end{aligned}
~~|`sse`|~~
\begin{aligned}
|do|~& |(z1, y0) <- any|\\
     & |z2 <- f y0|\\
     & |filt unlhd (z2, z1)|\\
     & |return (y0, z1)| \mbox{~~.}
\end{aligned}
\label{eq:monotonicity}
\end{equation}

\begin{theorem}[Greedy Theorem]
{\rm
Let |unlhd| be a binary relation on |b| that is reflexive and transitive.
and let |f :: a -> b -> P b| and |e :: P b|.
If |f x| is monotonic on |unlhd| for all |x|, we have
\begin{spec}
foldR (\x -> min_unlhd . f x) (min_unlhd e) {-"~"-}`sse`{-"~"-} min_unlhd . foldR f e {-"~~."-}
\end{spec}
} %rm
\end{theorem}

\subsection{Example: Segment with Maximum Sum}


The function |prefix| non-deterministically computes a prefix of the given list.
It can be defined inductively:
\begin{code}
prefix :: List a -> P (List a)
prefix []      = return []
prefix (x:xs)  = return [] <|> (x:) <$> prefix xs {-"~~,"-}
\end{code}
but we will use a |foldR|-based definition here:
\begin{spec}
prefix = foldR pre (return [])
   where pre x ys = return [] <|> return (x : ys) {-"~~."-}
\end{spec}
%if False
\begin{code}
pre x ys = return [] <|> return (x : ys)
\end{code}
%endif
Due to the way we define our |foldR|, the second definition returns |[]| more frequently.
The equivalence of the two definitions of |prefix| depends on
idempotency of the non-determinism monad.

Conversely, the function |suffix| non-deterministically returns a suffix of the given list:
\begin{code}
suffix :: List a -> P (List a)
suffix []      = return []
suffix (x:xs)  = return (x:xs) <|> suffix xs {-"~~."-}
\end{code}
We get all segments by |prefix <=< suffix|.

Let |max : P (List Int) -> P (List Int)| choose those lists having the largest sum.
The \emph{maximum segment sum} problem can be defined by:
\begin{code}
mss :: List Int -> P (List Int)
mss = max . (prefix <=< suffix) {-"~~."-}
\end{code}

We also define a monadic variation of |scanr|:
\begin{code}
scanR :: (a -> b -> P b) -> P b -> List a -> P (List b)
scanR f e []        = wrap <$> e
scanR f e (x : xs)  = do  ys <- scanR f e xs
                          z <- f x (head ys)
                          return (z : ys) {-"~~,"-}
\end{code}
where |wrap x = [x]|.
It is perhaps useful knowing that |scanR| is a |foldR|:
\begin{spec}
scanR f e = foldR f' (wrap <$> e)
  where f' x ys = do {z <- f x (head ys); return (z:ys)} {-"~~."-}
\end{spec}

\subsubsection{Properties of fold and scan}


To begin with, we need the property that:
%if False
\begin{code}
-- propHeadScanStmt :: (a -> b -> P b) -> P b -> List a -> P b
propHeadScanStmt f e xs =
   head <$> scanR f e xs === foldR f e xs
\end{code}
%endif
\begin{equation}
  |head <$> scanR f e xs === foldR f e xs| \mbox{~~.} \label{eq:HeadScan}
\end{equation}
\begin{proof}
Induction on |xs|. The case when |xs := []| is immediate.
For |xs := x:xs| we reason:
%if False
\begin{code}
-- propHeadScanStmt :: (a -> b -> P b) -> P b -> List a -> P b
propHeadScanPfInd f e x xs =
\end{code}
%endif
\begin{code}
      head <$> scanR f e (x : xs)
 ===  head <$> do  ys <- scanR f e xs
                   z <- f x (head ys)
                   return (z : ys)
 ===  do  ys <- scanR f e xs
          z <- f x (head ys)
          return z
 ===  do  ys <- scanR f e xs
          f x (head ys)
 ===  f x =<< (head <$> scanR f e xs)
 ===    {- induction -}
      f x =<< foldR f e xs
 ===  foldR f e (x : xs) {-"~~."-}
\end{code}
\end{proof}

We also need a \emph{scan lemma} for monadic fold and scan:
%if False
\begin{code}
propScanLemmaStmt :: (a -> b -> P b) -> P b -> List a -> P b
propScanLemmaStmt f e =
   foldR f e <=< suffix === member <=< scanR f e
\end{code}
%endif
\begin{equation}
  |foldR f e <=< suffix === member <=< scanR f e| \mbox{~~.}
  \label{eq:ScanLemma}
\end{equation}
\begin{proof}
Induction on the input. For the inductive case we reason:
%if False
\begin{code}
proofScanLemmaInd :: (a -> b -> P b) -> P b -> a -> List a -> P b
proofScanLemmaInd f e x xs =
\end{code}
%endif
\begin{code}
      foldR f e =<< suffix (x : xs)
 ===  foldR f e =<< (return (x:xs) <|> suffix xs)
 ===    {- |(=<<)| distributes into |(<||>)| -}
      (foldR f e =<< return (x:xs)) <|> (foldR f e =<< suffix xs)
 ===    {- induction -}
      foldR f e (x : xs) <|> (member =<< scanR f e xs)
 ===  (f x =<< foldR f e xs) <|> (member =<< scanR f e xs)
 ===    {- \eqref{eq:HeadScan}: |head <$> scanR f e xs === foldR f e xs| -}
      (f x =<< (head <$> scanR f e xs)) <|> (member =<< scanR f e xs)
 ===  do  ys <- scanR f e xs
          f x (head ys) <|> member ys
 ===    {- check this -}
      do  ys <- scanR f e xs
          z <- f x (head ys)
          return z <|> member ys
 ===  member =<< scanR f e (x : xs) {-"~~."-}
\end{code}
\end{proof}

Fold and scan with deterministic step functions are themselves deterministic:
\begin{align}
  |foldR (\x -> return . f x) (return e)| ~&=~ |return . foldr f e| \mbox{~~,}
    \notag\\
  |scanR (\x -> return . f x) (return e)| ~&=~ |return . scanr f e| \mbox{~~.}
    \label{eq:returnScanR}
\end{align}

\subsubsection{The Main Derivation}

The main derivation goes:
%if False
\begin{code}
-- derMSSMain :: (a -> b -> P b) -> P b -> a -> List a -> P b
derMSSMain =
\end{code}
%endif
\begin{code}
         max . (prefix <=< suffix)
 ===     max . ((max . prefix) <=< suffix)
 `spse`      {- greedy theorem -}
         max . (foldR maxPre (return []) <=< suffix)
 ===         {- scan lemma \eqref{eq:ScanLemma} -}
         max . (member <=< scanR maxPre (return []))
 `spse`      {- |maxPre x `spse` return . zplus x|, by \eqref{eq:returnScanR} -}
         max . (member <=< (return . scanr zplus []))
 ===         {- monad law -}
         max . member . scanr zplus []
 `spse`      {- \eqref{eq:MaxMaxList} -}
         return . maxlist . scanr zplus [] {-"~~."-}
\end{code}
where |maxPre :: a -> List a -> P (List a)| and
|zplus :: a -> List a -> List a| are given by:
\begin{code}
maxPre  x     = max . pre x {-"~~,"-}
zplus   x xs  = if x + sum xs < 0 then [] else (x:xs) {-"~~."-}
\end{code}

\paragraph{Use of Greedy Theorem}
The greedy theorem helps to establish that
%if False
\begin{code}
-- derMSSMain :: (a -> b -> P b) -> P b -> a -> List a -> P b
derMSPRes =
\end{code}
%endif
\begin{code}
  max . prefix `spse` foldR maxPre (return []) {-"~~."-}
\end{code}
Recall the greedy theorem:
%format y0
%format y1
%format b0
%format b1
\begin{spec}
min_R . foldr f e `spse` foldr (\x -> min_R . f x) (min_R e)
   <==  do  (y0, y1) <- any
            filt R (y0, y1)
            b1 <- f x y1
            return (y0, b1)  {-"~~"-}`sse`
          do  (b1, y0) <- any
              b0 <- f x y0
              filt R (b0, b1)
              return (y0, b1){-"~~."-}
\end{spec}
For the MSS problem, the monotonicity condition is proved below:
%if False
\begin{code}
-- derMSSMain :: (a -> b -> P b) -> P b -> a -> List a -> P b
proofMonoMSS x =
\end{code}
%endif

%format ys0
%format ys1
%format zs0
%format zs1

\begin{code}
        do  (ys0, ys1) <- any
            guard (ys0 `geqs` ys1)
            zs1 <- pre x ys1
            return (ys0, zs1)
 ===    do  (ys0, ys1) <- any
            guard (ys0 `geqs` ys1)
            zs1 <- (return [] <|> return (x : ys1))
            return (ys0, zs1)
 ===    do  (ys0, ys1) <- any
            guard (ys0 `geqs` ys1)
            return (ys0, []) <|> return (ys0, x : ys1)
 ===    do  (ys0, ys1) <- any
            (  do { return (ys0, []) } <|>
               do { guard (ys0 `geqs` ys1); return (ys0, x : ys1) } )
 ===      {- |(`geqs`)| monotonic w.r.t |(:)| -}
        do  (ys0, ys1) <- any
            (  do { guard ([] `geqs` []); return (ys0, []) } <|>
               do { guard ((x:ys0) `geqs` (x:ys1)); return (ys0, x : ys1) } )
 `sse`  do  (ys0, ys1) <- any
            zs0 <- (return [] <|> return (x:ys0))
            (  do { guard (zs0 `geqs` []); return (ys0, []) } <|>
               do { guard (zs0 `geqs` (x:ys1)); return (ys0, x : ys1) } )
 `sse`  do  (zs1, ys0) <- any
            zs0 <- (return [] <|> return (x:ys0))
            guard (zs0 `geqs` zs1)
            return (ys0, zs1)  {-"~~."-}
\end{code}

\subsection{Proof of the Greedy Theorem}


\begin{proof}
The aim is to prove that |foldR (\x -> min_unlhd . f x) (min_unlhd e) {-"~"-}`sse`{-"~"-} min_unlhd . foldR f e| if the monotonicity condition holds.

By the  fixed-point property \eqref{eq:foldR-comp}, we ought to prove
\begin{spec}
  (min_unlhd . f x) =<< min_unlhd (foldr f e xs) `sse`
    (min_unlhd . f x) =<< min_unlhd (foldR f e (x : xs)) {-"~~."-}
\end{spec}
\begin{spec}
     min_R . (f x <=< foldr f e) `spse`  (min_R . f x) <=< (min_R . foldr f e) {-"~~."-}
\end{spec}
Now we use the universal property. We focus on the second clause.
We use |do|-notation to implicitly invoke the monad laws, and commutative laws, behind-the-scene.
\begin{spec}
       do  xs <- any
           b0 <- (min_R . f x) =<< min_R (foldr f e xs)
           b1 <- f x =<< foldr f e xs
           return (b0, b1)
=      do  xs <- any
           y0 <- min_R (foldr f e xs)
           b0 <- min_R (f x y0)
           y1 <- foldr f e xs
           b1 <- f x y1
           return (b0, b1)
`sse`   {- |min|-cancelation -}
       do  (y0, y1) <- any
           filt R (y0, y1)
           b0 <- min_R (f x y0)
           b1 <- f x y1
           return (b0, b1)
`sse`   {- monotonicity -}
       do  (b1, y0) <- any
           b2 <- f x y0
           filt R (b2, b1)
           b0 <- min_R (f x y0)
           return (b0, b1)
`sse`   {- |min|-cancelation -}
       do  (b0, b1, b2) <- any
           filt R (b0, b2)
           filt R (b2, b1)
           return (b0, b1)
`sse`   {- |R| transitive -}
       do  (b0, b1) <- any
           filt R (b0, b1) {-"~~."-}
\end{spec}
\end{proof}

We have chosen to use the fixed-point property for the proof, to demonstrate more steps. We could have also used the fusion-theorem instead.
Recall the fusion condition:
\begin{spec}
  min_R . (f x =<<) `spse` (min_R . f x) <=< min_R {-"~~."-}
\end{spec}
By the universal property of |min|, we ought to prove:
\begin{spec}
do  ys <- any
    b0 <- (min_R . f x) =<< min_R ys
    b1 <- f x =<< ys
    return (b0, b1) `sse`
   do  (b0, b1) <- any
       filt R (b0, b1) {-"~~."-}
\end{spec}
The first step can be carried out by |min|-cancelation with |f := id|. The rest is the same.


\section{The Thinning Theorem}


The function |thin_Q| now has type |T b -> P (T b)|.
Its universal property is:
\begin{spec}
X `sse` thin_Q . collect . S <=>  (mem <=< X) `sse` S &&
                                  (do  a <- any
                                       t0 <- X a
                                       b1 <- S a
                                       return (t0, b1)) `sse`
                                    (do  (t0, b1) <- any
                                         b0 <- mem t0
                                         filt_Q (b0, b1)
                                         return (t0, b1)) {-"~~."-}
\end{spec}
%if False
\begin{code}
propThinUniv :: forall a (b :: Type) . (a -> P (T b)) -> (a -> P b) -> a -> P (T b)
propThinUniv x s =
    x `sse` thin_Q . collect . s
 where pre0 = (mem <=< x) `sse` s
       pre1 = (do a <- any
                  t0 <- x a
                  b1 <- s a
                  return (t0, b1)) `sse`
               (do (t0, b1) <- any
                   b0 <- mem t0
                   filt_Q (b0, b1)
                   return (t0, b1))
\end{code}
%endif
Letting |X = thin_Q . collect . S|, we have the cancelation law:
\begin{spec}
(do  a <- any
     t0 <- (thin_Q . collect) (S a)
     b1 <- S a
     return (t0, b1)) `sse`
  (do  (t0, b1) <- any
       b0 <- mem t0
       filt_Q (b0, b1)
       return (t0, b1)) {-"~~."-}
\end{spec}

The thinning theorem is given by:
\begin{spec}
thin_Q . collect . foldR f e `spse` foldR (\x -> thin_Q . collect . (f x <=< mem)) (thin_Q (collect e))
  <==  do  (y0, y1) <- any
         b1 <- f x y1
         filt_Q (y0, y1)
         return (y0, b1)  {-"~~"-}`sse`
       do  (b1, y0) <- any
           b2 <- f x y0
           filt_Q (b2, b1)
           return (y0, b1){-"~~."-}
\end{spec}
%if False
\begin{code}
thmThinning :: (a -> b -> P b) -> P b -> List a -> P (T b)
thmThinning f e =
  thin_Q . collect . foldR f e `spse`
    foldR (\x -> thin_Q . collect . (f x <=< mem))
       (thin_Q (collect e))
\end{code}
%endif

\subsection{Proof of the Thinning Theorem}

\begin{proof}
By the fixed-point property of |foldR|,
\begin{spec}
 (thin_Q . collect . (f x <=< mem)) =<< (thin_Q . collect . foldR f e) xs `sse`
    (thin_Q . collect . foldR f e) (x : xs)
<=>  {- definition of |foldR| -}
 (thin_Q . collect . (f x <=< mem)) =<< (thin_Q . collect . foldR f e) xs `sse`
    thin_Q (collect (f x =<< foldR f e xs))
<=>  {- abstracting away |xs| -}
  (thin_Q . collect . (f x <=< mem)) <=< (thin_Q . collect . foldR f e) `sse`
     thin_Q . collect . (f x <=< foldR f e) {-"~~."-}
\end{spec}
%if False
\begin{code}
propFixPoint0 :: (a -> b -> P b) -> P b -> a -> List a -> P (T b)
propFixPoint0 f e x xs =
  (thin_Q . collect . (f x <=< mem)) =<< (thin_Q . collect . foldR f e) xs
  `sse` (thin_Q . collect . foldR f e) (x : xs)

propFixPoint1 :: (a -> b -> P b) -> P b -> a -> List a -> P (T b)
propFixPoint1 f e x xs =
  (thin_Q . collect . (f x <=< mem)) =<< (thin_Q . collect . foldR f e) xs
  `sse` (thin_Q . collect . foldR f e) (x : xs)
  `sse` thin_Q (collect (f x =<< foldR f e xs))

propFixPoint2 :: (a -> b -> P b) -> P b -> a -> List a -> P (T b)
propFixPoint2 f e x  =
  (thin_Q . collect . (f x <=< mem)) <=< (thin_Q . collect . foldR f e)
  `sse` thin_Q . collect . (f x <=< foldR f e)
\end{code}
%endif
According to the universal property of |thin_Q|, we only need to show that
%if False
\begin{code}
pfThinThm2 :: (a -> b -> P b) -> P b -> a -> P (T b, b)
pfThinThm2 f e x =
\end{code}
%endif
\begin{code}
     do  xs <- any
         t0 <- (thin_Q . collect . (f x <=< mem)) =<< (thin_Q . collect . foldR f e) xs
         b1 <- f x =<< foldR f e xs
         return (t0, b1)
===  do  xs <- any
         u0 <- (thin_Q . collect) (foldR f e xs)
         t0 <- (thin_Q . collect . (f x <=< mem)) u0
         y1 <- foldR f e xs
         b1 <- f x y1
         return (t0, b1)
`sse`  {- |thin| cancelation -}
     do  (u0, y1) <- any
         y0 <- mem u0
         t0 <- (thin_Q . collect . (f x <=< mem)) u0
         filt_Q (y0, y1)
         b1 <- f x y1
         return (t0, b1)
`sse`  {- monotonicity -}
     do  (u0, b1) <- any
         y0 <- mem u0
         b2 <- f x y0
         filt_Q (b2, b1)
         t0 <- (thin_Q . collect . (f x <=< mem)) u0
         return (t0, b1)
===    {- monad laws -}
     do  (u0, b1) <- any
         b2 <- (f x <=< mem) u0
         t0 <- (thin_Q . collect . (f x <=< mem)) u0
         filt_Q (b2, b1)
         return (t0, b1)
`sse`  {- cancelation -}
     do  (t0, b2, b1) <- any
         b0 <- mem t0
         filt_Q (b0, b2)
         filt_Q (b2, b1)
         return (t0, b1)
`sse`  {- transitivity of |Q| -}
     do  (t0, b1) <- any
         b0 <- mem t0
         filt_Q (b0, b1)
         return (t0, b1) {-"~~."-}
\end{code}
Note that the second "monotonicity" step is not quite the same as the
monotonicity assumption --- |y0| is not drawn from |any|, but a result of
|mem u0|. This is fine because
|do {y0 <- mem u0 ...} | can be rewritten as
|do {y0' <- mem u0; y0 <- any; filt (=) y0 y0' ... }|.
\end{proof}

\subsection{Example: Knapsack}

\todo{Or MSS with upper bound on length?}

\section{Conclusions}

\bibliographystyle{jfplike}
\bibliography{monadic-opt.bib}
%\input{sublists.bbl}


\end{document}
