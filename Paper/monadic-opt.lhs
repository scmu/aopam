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
%format b1'
%format y0
%format y1
%format y2
%format z0
%format z1
%format z2
%format t0
%format t1
%format u0
%format u1
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
\label{sec:intro}

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
  max . (filt p <=< foldR f e) {-"~~."-}
\end{spec}
where |(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)| is Kliseli composition and |(.)| is ordinary function composition.
Given an input of type |List A|, the collection of all solution candidates is generated by |foldR f e :: List A -> M B|, a monadic variation of fold on lists.
The function |filt :: (b -> Bool) -> b -> M b| keeps those satisfies predicate |p|, and |max :: M b -> M b| keeps only those having maximum value under some chosen ordering.
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

Non-determinism is the only effect we are concerned with in this article: |M a| denotes a non-deterministic computation that may yield zero, one, or more values of type |a|.
We let |mplus :: M a -> M a -> M a| denote non-deterministic choice and |mzero :: M a| failure. Together they form a monoid (that is, |mplus| is associative with |mzero| as its identity element) and satisfy the following laws:
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

\subsection{Maximum}

Consider a binary relation |unlhd| on some type |a|.
A value |y :: a| is a maximum of |xs :: P a| if |y| is in |xs|, and for every element |x `elem` xs| we have |y `unrhd` x|.
The definition itself does not assume much from |unlhd|.
In particular, since |unlhd| is not unnecessarily anti-symmetric, maximum elements might not be unique.
The function |max_unlhd :: P a -> P a| takes a set and returns a refined set that keeps all the maximum elements and nothing else.
In set-theoretical notation, |max_unlhd| can be defined by the following equivalence:
for all |xs| and |ys|,
\begin{equation}
|ys `sse` max_unlhd xs {-"~"-}<==>{-"~"-} ys `sse` xs && (forall y `mem` ys : (forall x `mem` xs : y `unrhd` x)) {-"~~."-}|
\label{eq:max-def-set}
\end{equation}
We omit the subscript |unlhd| when it is clear from the context or not relevant.
The |(==>)| direction of \eqref{eq:max-def-set}, letting |ys = max xs|, says that |max xs| is a subset of |xs|, and every member in |max xs| is no lesser than any member in |xs|. The |(<==)| direction of \eqref{eq:max-def-set} says that |max xs| is the largest such set --- any |ys| satisfying the righthand side is a subset of |max xs|.

In calculation, we often want to refine expressions of the form |max . f| where |f| generates a set. Therefore the following \emph{universal property} of |max| is more useful: for all |h| and |f| of type |a -> P b|,
\begin{equation}
|h `sse` max_unlhd . f {-"~"-}<==>{-"~"-} h `sse` f && (forall x : (forall y1 `mem` h x : (forall y0 `mem` f x : y1 `unrhd` y0))) {-"~~."-}|
\label{eq:max-univ-set}
\end{equation}
Properties \eqref{eq:max-def-set} and \eqref{eq:max-univ-set} are equivalent.
\todo{argue for that}

The aim of our work, however, is to capture the ideas above in a monadic notation, such that programs can be manipulated and reasoned about in the monadic language.
It turns out that \eqref{eq:max-univ-set} can be rewritten monadically as below:
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
|h `sse` max_unlhd . f|\mbox{~~}|<==>|\mbox{~~} |h `sse` f &&|~
\setlength{\jot}{-1pt}
\left(
 \begin{aligned}
 |do|~ & |x <- any| \\
       & |y1 <- h x| \\
       & |y0 <- f x| \\
       & |return (y1, y0)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(y1, y0) <- any| \\
       & |filt unrhd (y1, y0)|
 \end{aligned}
 \right)\mbox{~~.}
 \label{eq:max-univ-monadic}
\end{equation}
In \eqref{eq:max-univ-monadic} and from now on we abuse the notation a bit,
using |filt unrhd| to denote |filt (\(y,z) -> y `unrhd` z)|.
The large pair of parentheses in \eqref{eq:max-univ-monadic} relates two monadic values. On the lefthand side we generate a pair of values |y1| and |y0|, which are respectively results of |h| and |f| for the same, arbitrarily generated input |x|. The inclusion says that |(y1, y0)| must be contained by the monad on the righthand side, which consists of all pairs |(y1, y0)| as long as |y1 `unrhd` y0|.

Letting |h = max| and |f = id| in \eqref{eq:max-univ-monadic}, we get |max `see` id| on the righthand side.
Letting |h = max . f| in \eqref{eq:max-univ-monadic}, we get on the righthand side the |max|-cancelation law:
\begin{equation}
\setlength{\jot}{-1pt}
 \begin{aligned}
 |do|~ & |x <- any| \\
       & |y1 <- max (f x)| \\
       & |y0 <- f x| \\
       & |return (y1, y0)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(y1, y0) <- any| \\
       & |filt unrhd (y1, y0)| \mbox{~~.}
 \end{aligned}
 \label{eq:max-cancelation}
\end{equation}

By defining the ``split'' operator |split f g x = do { y <- f x; z <- g x; return (y,z) }|,
\eqref{eq:max-univ-monadic} can be written more concisely as below:
\begin{equation*}
|h `sse` max_unlhd . f|\mbox{~~}|<==>|\mbox{~~} |h `sse` f &&|~
|split h f =<< any {-"\,"-}`sse`{-"\,"-} filt unrhd =<< any| \mbox{~~.}
\end{equation*}
We may then manipulate expressions using properties of the |split| operator.
The |max|-cancelation law is written as
|split (max_unlhd . f) f =<< any {-"\,"-}`sse`{-"\,"-} filt unrhd =<< any|.

Note again that |max_unlhd| does not assume much from |unlhd|.
It is likely that there is no maximum in a set |xs| --- there is no element that is larger than every other element with respect to |unlhd|.
In that case |max_unlhd xs| reduces to empty set (that is, |fail|).
That is fine at the specification stage,
although we might not be able to refine this specification to a total function.
We will discuss about that soon.

% Maximum is defined as the dual of minimum:
% \begin{spec}
%   max_unlhd = min_unrhd {-"~~."-}
% \end{spec}

\paragraph*{Promotion into Kliseli Composition.}~
The function |max| promotes into |join|:
%if False
\begin{code}
-- propMinJoin :: forall {k} (a :: Type). P (P a) -> P a
propMaxJoin xss = max (join xss) === max (join (fmap max xss))
\end{code}
%endif
\begin{equation}
  |max . join === max . join  . fmap max| \mbox{~~.}
   \label{eq:MaxJoin}
\end{equation}
Consider an input |xss :: P (P a)|, a set of sets, as the input for both sides. On the lefthand side, |xss| is joined into a single set, from which we keep the minimums. It is equivalent to the righthand side, where we choose the minimums of each of the sets in |xss|, before keeping their minimums.
With \eqref{eq:MaxJoin} and the definition of |(>>=)| by |join| we can show how |max| promotes into |(=<<)| or |(<=<)|:
\begin{equation}
  |max . (f <=< g) === max . ((max . f) <=< g)| \mbox{~~.}
   \label{eq:MaxKComp}
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

In the last few steps of a program calculation we usually want to refine a monadic |max| to a function on lists.
If |unlhd| is total (that is, for all |x| and |y| of the right type, at least one of |x `unrhd` y| or |y `unrhd` x| holds), and if |xs| is non-empty, we have
\begin{equation}
 |return (maxlist xs) `sse` max_unlhd (member xs) | \label{eq:MaxMaxList}
\end{equation}
where |maxlist| is some implementation of maximum on lists, e.g.
\begin{spec}
  maxlist :: List a -> a
  maxlist [x] = x
  maxlist (x : y : xs) = x `bmax` maxlist (y : ys) {-"~~,"-}
   where x `bmax` y  =if x `unrhd` y then x else y {-"~~."-}
\end{spec}
That |unlhd| being total guarantees that maximum exists for non-empty |xs|.
The function |maxlist| may decide how to resolve a tie --- in the implementation above, for example, |maxlist| prefers elements that appears earlier in the list.

\paragraph*{In the Agda Model}
we implement |min| by:

\todo{more here.}

It is then proved in Agda that the above implementation satisfies \eqref{eq:min-univ-monadic}.

\section{The Greedy Theorem}

As stated in Section \ref{sec:intro}, this article focuses on problems of the form:
\begin{spec}
  max_unlhd . (filt p <=< foldR f e) {-"~~,"-}
\end{spec}
that is, problems whose solution candidates can be generated by a monadic fold.
In |foldR|, given the current element |x :: a| of the list, the function |f x :: b -> P b| takes a candidate of type |b| and extends it in all possible ways.
If certain conditions hold, however, we would not need all of them, but the locally best one.

Recall that we aim to compute the maximum solutions under ordering |unlhd|.
Therefore, when |y1 `unrhd` y0|, we call |y1| the preferred solution, and |y0| the (possibly) lesser one.
A function |f : b -> P b| is said to be \emph{monotonic on |unrhd|} if the following holds:
\begin{equation}
\setlength{\jot}{-1pt}
\begin{aligned}
|do|~ & |(y1, y0) <- any|\\
      & |filt unrhd (y1, y0)|\\
      & |z0 <- f y0| \\
      & |return (y1, z0)|
\end{aligned}
~~|`sse`|~~
\begin{aligned}
|do|~& |(y1, z0) <- any|\\
     & |z1 <- f y1|\\
     & |filt unrhd (z1, z0)|\\
     & |return (y1, z0)| \mbox{~~.}
\end{aligned}
\label{eq:monotonicity}
\end{equation}
On the lefthand side of \eqref{eq:monotonicity} we generate a pair of values |(y1, y0)| with the constraint that |y0| is possibly lesser.
Then we let |z0| be \emph{any} result we generate by |f| from the lesser solution |y0|, and return the pair |(y1, z0)|.
The inclusion means that nothing in the lefthand side is missing in the righthand side. The righthand side must be able to generate this particular pair |(y1, z0)|, that is, for this |(y1, z0)| the |filt| in the righthand side must succeed at least once.
Therefore, there must \emph{exist} some |z1| generated from |y1|, the preferred solution, such that |z1 `unrhd` z0|.

Property \eqref{eq:monotonicity} is an encoding of
\begin{spec}
  (forall y1, y0, z0 : y1 `unrhd` y0 && z0 `elem` f y0 ==> (exists z1 : z1 `elem` f y1 && z1 `unrhd` z0)) {-"~~."-}
\end{spec}

When \eqref{eq:monotonicity} holds for |f|, in |foldR f e| we can safely drop the lesser solution |y0|, knowing that for any solution it may generate, |y1| always yields something that is at least as good. In fact, in each step of |foldR| we need to keep only the currently most preferred solutions.
This is formalised by the following Greedy Theorem:
\begin{theorem}[Greedy Theorem]
\label{thm:greedy}
{\rm
Let |unlhd| be a binary relation on |b| that is reflexive and transitive.
and let |f :: a -> b -> P b| and |e :: P b|.
If |f x| is monotonic on |unrhd| for all |x|, we have
\begin{equation}
|foldR (\x -> max_unlhd . f x) (max_unlhd e) {-"~"-}`sse`{-"~"-} max_unlhd . foldR f e {-"~~."-}|
\label{eq:greedy}
\end{equation}
} %rm
\end{theorem}

The specification on the righthand side can be refined to a |foldR| in which we apply |max| in every step. The algorithm still keeps a set of all maximums. It is in fact sufficient to keep only \emph{one} maximum solution, but the decision of which one to keep can be postponed when we further refine the lefthand side to a function.

\subsection{Proof of the Greedy Theorem}

To most users, what matters is how the Greedy Theorem can be put to use to solve actual problems.
But, having introduced something as awkward as \eqref{eq:monotonicity}, we would like to see how it helps to prove the theorem. It will turn out that \eqref{eq:monotonicity} fits quite well into the proof of Theorem \ref{thm:greedy}.

\begin{proof}
The aim is to prove \eqref{eq:greedy} given that the monotonicity condition holds.
There are various ways one can proceed.
We may apply both sides of \eqref{eq:greedy} to a list, and go with a usual inductive proof.
To go for the most concise proof one may use the |foldR| fusion theorem.
We will go for something in the middle: using the fixed-point property \eqref{eq:foldR-comp}. This way we do not get the shortest proof, but we get to demonstrate more tricks that may be useful in reasoning about monadic programs.

By the fixed-point property \eqref{eq:foldR-comp}, to establish \eqref{eq:greedy} we ought to prove that
\begin{spec}
  max e `sse` max (foldR f e []) &&
  (max . f x) =<< max (foldR f e xs) `sse` max (foldR f e (x : xs)) {-"~~."-}
\end{spec}
The first inclusion is immediate. The second expands to
\begin{spec}
  (max . f x) =<< max (foldR f e xs) `sse` max (f x =<< foldR f e xs) {-"~~."-}
\end{spec}
Abstracting |xs| away, we get
\begin{spec}
 (max . f x) <=< (max . foldR f e) `sse` max . (f x <=< foldR f e)    {-"~~,"-}
\end{spec}
which matches the form of the universal property \eqref{eq:max-univ-monadic} with |h := (max . f x) <=< (max . foldR f e)| and |f := f x <=< foldR f e|.
The first conjunct in the righthand side of \eqref{eq:max-univ-monadic}, that
|(max . f x) <=< (max . foldR f e) `sse` f x <=< foldR f e|
follows from that |max `sse` id|.
For the second conjunct, we need to prove that:
\begin{equation*}
\setlength{\jot}{-1pt}
 \begin{aligned}
 |do|~ & |xs <- any| \\
       & |y1 <- (max . f x) =<< max (foldR f e xs)| \\
       & |y0 <- f x =<< foldR f e xs| \\
       & |return (y1, y0)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(y1, y0) <- any| \\
       & |filt unrhd (y1, y0)|
 \end{aligned}\mbox{~~.}
\end{equation*}
It is usually easier to start from the smaller side (the lefthand side) and stepwise relaxing to to a larger monad. Using associative of |(=<<)| and definition of |do|-notation, the lefthand side expands to:
\begin{spec}
do  xs <- any
    b1 <- max (foldR f e xs)
    y1 <- max (f x b1)
    b0 <- foldR f e xs
    y0 <- f x b0
    return (y1, y0) {-"~~."-}
\end{spec}
Having both |max (foldR f e xs)| and |foldR f e xs| inspires us to use the |max|-cancelation law.
To use the law, notice that lines generating |xs|, |b1|, and |b0| match that of the lefthand side of \eqref{eq:max-cancelation}, therefore we rewrite them accordingly to the righthand side:
\begin{spec}
       ...
`sse`   {- |max|-cancelation -}
       do  (b1, b0) <- any
           filt unrhd (b1, b0)
           y1 <- max (f x b1)
           y0 <- f x b0
           return (y1, y0) {-"~~."-}
\end{spec}
If we were calling |f x b1| instead of |f x b0|, we would be able to use |max|-cancelation again.
That is exactly what monotonicity offers us: it assures that, instead of applying |f x| to |b0|, we lose nothing by applying |f x| to the preferred solution |b1|.
To make use of monotonicity, notice that the lines generating |(b1, b0)| and |y0| and the |filt unrhd (b1, b0)| match the lefthand side of \eqref{eq:monotonicity}, therefore we rewrite them to the righthand side of \eqref{eq:monotonicity}:
\begin{spec}
       ...
`sse`   {- monotonicity -}
       do  (b1, y0) <- any
           z1 <- f x b1
           filt unrhd (z1, y0)
           y1 <- max (f x b1)
           return (y1, y0) {-"~~."-}
\end{spec}
Now we can use |max|-cancelation again to cancel |max (f x b1)| and |f x b1|:
\begin{spec}
       ...
`sse`   {- |max|-cancelation -}
       do  (y1, y0, z1) <- any
           filt unrhd (y1, z1)
           filt unrhd (z1, y0)
           return (y1, y0)
`sse`   {- |unrhd| transitive -}
       do  (y1, y0) <- any
           filt unrhd (y1, y0) {-"~~."-}
\end{spec}
The last step uses transitivity of |unrhd|, and then we are done.

% \begin{spec}
%        do  xs <- any
%            y1 <- (max . f x) =<< max (foldR f e xs)
%            y0 <- f x =<< foldR f e xs
%            return (y1, y0)
% =        {- monad-laws, |do|-notation -}
%        do  xs <- any
%            b1 <- max (foldR f e xs)
%            y1 <- max (f x b1)
%            b0 <- foldR f e xs
%            y0 <- f x b0
%            return (y1, y0)
% `sse`   {- |max|-cancelation -}
%        do  (b1, b0) <- any
%            filt unrhd (b1, b0)
%            y1 <- max (f x b1)
%            y0 <- f x b0
%            return (y1, y0)
% `sse`   {- monotonicity -}
%        do  (b1, y0) <- any
%            z1 <- f x b1
%            filt unrhd (z1, y0)
%            y1 <- max (f x b1)
%            return (y1, y0)
% `sse`   {- |max|-cancelation -}
%        do  (y1, y0, z1) <- any
%            filt unrhd (y1, z1)
%            filt unrhd (z1, y0)
%            return (y1, y0)
% `sse`   {- |unrhd| transitive -}
%        do  (y1, y0) <- any
%            filt unrhd (y1, y0) {-"~~."-}
% \end{spec}
\end{proof}
We use |do|-notation to implicitly invoke the monad laws, and commutative laws, behind-the-scene.

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

\subsection{Example: Segment with Maximum Sum}

To see an application of the Greedy Theorem, we consider the classical maximum segment sum again,
but return the list instead of the sum.
The reason for reviewing an old problem is to see whether our usual pattern of problem solving:
factor segment problems into prefix-of-suffix problems, using ``scan'', etc,
adapt smoothly into our new setting.

Typically, to solve a problem on segments, we see it as solving a problem on prefixes for each of the suffixes of the input.
The function |prefix| non-deterministically computes a prefix of the given list:
\begin{code}
prefix :: List a -> P (List a)
prefix []      = return []
prefix (x:xs)  = return [] <|> (x:) <$> prefix xs {-"~~."-}
\end{code}
Instead of the inductive definition above, we will use a |foldR|-based definition here:
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

Let |geqs| be defined by |xs `geqs` ys = sum xs >= sum ys|, therefore
|max_leqs : P (List Int) -> P (List Int)| choose those lists having the largest sum.
The \emph{maximum segment sum} problem can be defined by:
\begin{code}
mss :: List Int -> P (List Int)
mss = max_leqs . (prefix <=< suffix) {-"~~."-}
\end{code}


\subsubsection{Scan and Its Properties}

A key step in speeding up the algorithm to |mss| is introducing |scanr|.
For this article, we define a monadic variation of |scanr|:
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

We will need a number of properties relating scan and fold.
To begin with:
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
 ===    {- definition of |scanR| -}
      head <$> do  ys <- scanR f e xs
                   z <- f x (head ys)
                   return (z : ys)
 ===    {- definition of |(<$>)|, monad laws -}
      do  ys <- scanR f e xs
          z <- f x (head ys)
          return z
 ===    {- monad law -}
      do  ys <- scanR f e xs
          f x (head ys)
 ===    {- |do|-notation -}
      f x =<< (head <$> scanR f e xs)
 ===    {- induction -}
      f x =<< foldR f e xs
 ===    {- definition of |foldR| -}
      foldR f e (x : xs) {-"~~."-}
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
 ===    {- definitions of |scanR| and |member| -}
      member =<< scanR f e (x : xs) {-"~~."-}
\end{code}
\end{proof}

Finally, from \eqref{eq:foldr-foldR} one can induce that |scarnR| with a
deterministic step function is itself deterministic:
\begin{align}
  |scanR (\x -> return . f x) (return e)| ~&=~ |return . scanr f e| \mbox{~~.}
    \label{eq:scanr-scanR}
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
 `spse`      {- |maxPre x `spse` return . zplus x|, by \eqref{eq:scanr-scanR} -}
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

\paragraph*{Use of Greedy Theorem}
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
% Recall the greedy theorem:
% %format y0
% %format y1
% %format b0
% %format b1
% \begin{spec}
% min_R . foldr f e `spse` foldr (\x -> min_R . f x) (min_R e)
%    <==  do  (y0, y1) <- any
%             filt R (y0, y1)
%             b1 <- f x y1
%             return (y0, b1)  {-"~~"-}`sse`
%           do  (b1, y0) <- any
%               b0 <- f x y0
%               filt R (b0, b1)
%               return (y0, b1){-"~~."-}
% \end{spec}
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
        do  (ys1, ys0) <- any
            filt geqs (ys1, ys0)
            zs0 <- pre x ys0
            return (ys1, zs0)
 ===       {- definition of |pre| -}
        do  (ys1, ys0) <- any
            filt geqs (ys1, ys0)
            zs0 <- (return [] <|> return (x : ys0))
            return (ys1, zs0)
 ===       {- monad laws -}
        do  (ys1, ys0) <- any
            filt geqs (ys1, ys0)
            return (ys1, []) <|> return (ys1, x : ys0)
 ===       {- |(>>=)| distributes into |(<||>)|, since |ys1 `geqs` []| -}
        do  (ys1, ys0) <- any
            (  do { return (ys1, []) } <|>
               do { filt geqs (ys1, ys0); return (ys1, x : ys0) } )
 ===       {- |geqs| monotonic w.r.t |(:)| -}
        do  (ys1, ys0) <- any
            (  do { filt geqs ([], []); return (ys1, []) } <|>
               do { filt geqs (x:ys1, x:ys0); return (ys1, x : ys0) } )
 `sse`  do  (ys1, ys0) <- any
            zs1 <- (return [] <|> return (x:ys1))
            (  do { filt geqs (zs1, []); return (ys1, []) } <|>
               do { filt geqs (zs1, x:ys0); return (ys1, x : ys0) } )
 `sse`  do  (ys1, zs0) <- any
            zs1 <- (return [] <|> return (x:ys1))
            filt geqs (zs1, zs0)
            return (ys1, zs0)  {-"~~."-}
\end{code}

\section{The Thinning Theorem}


The function |thin_preceq| now has type |T b -> P (T b)|.
Its universal property is:
\begin{equation}
\setlength{\jot}{-1pt}
\begin{split}
|h `sse` thin_preceq . collect . f |\mbox{~~}|<==>|&\mbox{~~} |(mem <=< h) `sse` f &&|\\
&
\left(
 \begin{aligned}
 |do|~ & |x <- any| \\
       & |t1 <- h x| \\
       & |y0 <- f x| \\
       & |return (t1, y0)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(t1, y0) <- any| \\
       & |y1 <- mem t1| \\
       & |filt succeq (y1, y0)|\\
       & |return (t1, y0)|
 \end{aligned}
 \right)\mbox{~~.}
 \label{eq:thin-univ-monadic}
\end{split}
\end{equation}
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
Letting |h = thin_preceq . collect . f|, we have the cancelation law:
\begin{equation}
\setlength{\jot}{-1pt}
  \begin{aligned}
  |do|~ & |x <- any| \\
        & |t1 <- thin_preceq (collect (f x))| \\
        & |y0 <- f x| \\
        & |return (t1, y0)|
  \end{aligned}
  |`sse`|~~
  \begin{aligned}
  |do|~ & |(t1, y0) <- any| \\
        & |y1 <- mem t1| \\
        & |filt succeq (y1, y0)|\\
        & |return (t1, y0)|
  \end{aligned}
\end{equation}


The thinning theorem is given by:
\begin{theorem}[Thinning Theorem]
\label{thm:thinning}
{\rm Let |preceq| be a binary relation on |b| that is reflexive and transitive,
and let |f :: a -> b -> P b| and |e :: P b|.
If |f x| is monotonic on |succeq| for all |x|, we have
\begin{equation}
\setlength{\jot}{-1pt}
\begin{split}
&|foldR (\x -> thin_preceq . collect . (f x <=< mem)) (thin_preceq (collect e)) `sse`| \\
& \qquad  |thin_preceq . collect . foldR f e  {-"~~."-}|
\end{split}
\label{eq:thinning}
\end{equation}
}
%if False
\begin{code}
thmThinning :: (a -> b -> P b) -> P b -> List a -> P (T b)
thmThinning f e =
  thin_Q . collect . foldR f e `spse`
    foldR (\x -> thin_Q. collect . (f x <=< mem))
       (thin_Q (collect e))
\end{code}
%endif
\end{theorem}

\subsection{Proof of the Thinning Theorem}

\begin{proof}
By the fixed-point property of |foldR| \eqref{eq:foldR-comp}, to prove \eqref{eq:thinning} it is sufficient to show that:
\begin{spec}
     (thin_preceq . collect . (f x <=< mem)) =<< (thin_preceq . collect . foldR f e) xs `sse`
       (thin_preceq . collect . foldR f e) (x : xs)
<=>      {- definition of |foldR| -}
     (thin_preceq . collect . (f x <=< mem)) =<< (thin_preceq . collect . foldR f e) xs `sse`
       thin_preceq (collect (f x =<< foldR f e xs))
<=>     {- abstracting away |xs| -}
     (thin_preceq . collect . (f x <=< mem)) <=< (thin_preceq . collect . foldR f e) `sse`
       thin_preceq . collect . (f x <=< foldR f e) {-"~~."-}
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
According to the universal property of |thin_preceq|, for the above to hold we need to show that
\begin{spec}
  mem <=< (thin_preceq . collect . (f x <=< mem)) <=< (thin_preceq . collect . foldR f e) `sse` f x <=< foldR f e {-"~~,"-}
\end{spec}
and that
%if False
\begin{code}
pfThinThm2 :: (a -> b -> P b) -> P b -> a -> P (T b, b)
pfThinThm2 f e x =
\end{code}
%endif
\begin{code}
     do  xs <- any
         t1 <- (thin_preceq . collect . (f x <=< mem)) =<< (thin_preceq . collect . foldR f e) xs
         y0 <- f x =<< foldR f e xs
         return (t1, y0)
===  do  xs <- any
         u1 <- (thin_preceq . collect) (foldR f e xs)
         t1 <- (thin_preceq . collect . (f x <=< mem)) u1
         b0 <- foldR f e xs
         y0 <- f x b0
         return (t1, y0)
`sse`  {- |thin| cancelation -}
     do  (u1, b0) <- any
         b1 <- mem u1
         filt preceq (b1, b0)
         t1 <- (thin_preceq . collect . (f x <=< mem)) u1
         y0 <- f x b0
         return (t1, y0)
`sse`  {- monotonicity -}
     do  (u1, y0) <- any
         b1 <- mem u1
         y1 <- f x b1
         filt preceq (y1, y0)
         t1 <- (thin_preceq . collect . (f x <=< mem)) u1
         return (t1, y0)
===    {- monad laws -}
     do  (u1, y0) <- any
         y1 <- (f x <=< mem) u1
         filt preceq (y1, y0)
         t1 <- (thin_preceq . collect . (f x <=< mem)) u1
         return (t1, y0)
`sse`  {- |thin| cancelation -}
     do  (y0, t1, y1) <- any
         y2 <- mem t1
         filt preceq (y2, y1)
         filt preceq (y1, y0)
         return (t1, y0)
`sse`  {- transitivity of |preceq| -}
     do  (y0, t1) <- any
         y2 <- mem t1
         filt preceq (y2, y0)
         return (t1, y0) {-"~~."-}
\end{code}
Note that the second "monotonicity" step is not quite the same as the
monotonicity assumption --- |b1| is not drawn from |any|, but a result of
|mem u1|. This is fine because
|do {b1 <- mem u1 ...} | can be rewritten as
|do {b1' <- mem u1; b1 <- any; filt (=) b1 b1' ... }|.
\end{proof}

\subsection{Example: Knapsack}

\todo{Or MSS with upper bound on length?}

\section{Conclusions}

\bibliographystyle{jfplike}
\bibliography{monadic-opt.bib}
%\input{sublists.bbl}


\end{document}
