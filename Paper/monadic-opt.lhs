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

Textbook examples of program calculation for such optimisation problems tend to return the optimal value (in this case, the sum), rather than the solution that yields the optimal value (the list),
because this approach would not be feasible otherwise.
When there are multiple solutions that yield the optimal value.
the specification, being a function, has to pick a particular one, which the implementation has to return.
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
A function |a -> b| can be lifted to monad |M| by the operator |(<$>)|:
\begin{spec}
(<$>) :: (a -> b) -> M a -> M b
f <$> m = m >>= (return . f) {-"~~."-}
\end{spec}
It follows easily from the monad laws that
|id <$> m = m| and |(f . g) <$> m = f <$> (g <$> m)|, that is, |M| is a functor with |(<$>)| as its functorial map.

In this paper we will also make extensive use of the reverse bind and the Kliseli composition:
\begin{spec}
(=<<) :: (a -> M b) -> M a -> M b
f =<< m = m >>= f {-"~~,"-}

(<=<) :: (b -> M c) -> (a -> M b) -> (a -> M c)
(f <=< g) x = f =<< g x {-"~~."-}
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
|mzero| is the empty set, |mplus| is set union, |(`sse`)| is set inclusion, |return| forms a singleton set, and |m >>= f| is given by |union {f x || x <- m }|.
For the rest of the paper we take |M = P|.

The set |any : P a| contains all elements having type |a|.
Computationally, it creates an arbitrary element of its type.
The command |filt : (a -> Bool) -> a -> P a| is defined by
\begin{spec}
filt p x  | p x        = return x
          | otherwise  = fail {-"~~."-}
\end{spec}
It returns its input |x| if it satisfies |p|, and fails otherwise.

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
\begin{equation*}
|foldR f0 e0 `sse` foldR f1 e1 {-"~"-}<=={-"~"-} f0 `sse` f1 && e0 `sse` e1  {-"~~."-}|
\end{equation*}
Note that in |f0 `sse` f1|, set inclusion is lifted to denote |f0 x y `sse` f1 x y| for all |x| and |y|.

Finally, monadic |foldR| can be refined to pure |foldr| if both of its arguments are pure:
\begin{equation*}
|return (foldr f e) = foldR (\x -> return . f x) (return e) {-"~~."-}|
\end{equation*}

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

\section{Proof of the Greedy Theorem}


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

\bibliographystyle{jfplike}
\bibliography{monadic-opt.bib}
%\input{sublists.bbl}


\end{document}
