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
& \mbox{{\bf left identity}:}  & |return x >>= f| &= |f x| \mbox{~~,}\\
& \mbox{{\bf right identity}:} & |m >>= return| &= |m|  \mbox{~~,}\\
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

Non-determinism is the only effect we are concerned with in this article.
For that we introduce two operators |mzero :: M a| and |mplus :: M a -> M a -> M a| that form a monoid (that is, |mplus| is associative with |mzero| as its identity element) and satisfy the following laws:
\begin{align*}
  |mzero >>= f| &= |mzero| \mbox{~~,}\\
  |f >> mzero|  &= |mzero| \mbox{~~,}\\
  |m >>= (\x -> f x `mplus` g x)| &= |(m >>= f) `mplus` (m >>= g)| \mbox{~~,}\\
  |(m `mplus` n) >>= f| &= |(m >>= f) `mplus` (n >>= f)| \mbox{~~.}
\end{align*}
Furthermore, |mplus| is assumed to be idempotent: |m `mplus` m = m|.

The inclusion relation of non-determinism monad is defined by:
\begin{spec}
m `sse` n = (m `mplus` n = n) {-"~~."-}
\end{spec}
We also lift the relation to functions: |f `sse` g = (forall x : f x `sse` g x)|.

A structure that supports all the operations above is the set monad: for all type |a|,
|m :: P a| is a set whose elements are of type |a|,
|mzero| is the empty set, |mplus| is set union, |(`sse`)| is set inclusion, |return| forms a singleton set, and |m >>= f| is given by |union {f x || x <- m }|.
For the rest of the paper we take |M = P|.

The set |any :: P a| contains all elements having type |a|. Computationally, it creates an arbitrary element of an apporpriate type.
The command |filt :: (a -> Bool) -> a -> P a| is defined by
\begin{spec}
filt p x  | p x        = return x
          | otherwise  = fail {-"~~."-}
\end{spec}

\subsection{The Agda Model of Set Monad}

To ensure that there is indeed a model of our set monad, we built one in Agda.
A first attempt was to represent |P| by a predicate:
\begin{spec}
P : Set -> Set1
P a = a -> Set {-"~~,"-}
\end{spec}
and define |return| and |(>>=)| by
\begin{spec}
return x x' = x <=> x' {-"~~,"-}
(m >>= f) y = exists ((\ x -> m x * f x y)) {-"~~."-}
\end{spec}
We would soon get stuck when we try to prove any of its properties.
To prove the right identity law, for example, amounts to proving that
\begin{spec}
  (\y -> exists ((\x -> m x * x <=> y))) <=> m {-"~~."-}
\end{spec}


\subsection{Monadic Fold}

\begin{spec}
foldr :: (a -> b -> m b) -> m b -> List a -> m b
foldr f e []      = e
foldr f e (x:xs)  = f x =<< foldr f e xs {-"~~."-}
\end{spec}


\begin{spec}
  h . foldr f e `spse` foldr g (h e) {-"\,"-}<=={-"\,"-} h (f x =<< m) `spse` g x =<< h m {-"~~"-}
\end{spec}

\paragraph*{Minimum}




The new universal property of |min| is given by:
%\begin{spec}
%X `sse` min_R . f {-"\,"-}<=> {-"\,"-}  X `sse` f &&
%                                        (  do  a   <- any
%                                               b0  <- X a
%                                               b1  <- f a
%                                               return (b0, b1) {-"\,"-} `sse`
%                                                 do  (b0, b1) <- any
%                                                     filt R (b0, b1) {-"\,"-}) {-"~~."-}
%\end{spec}
\begin{equation*}
|X `sse` min_R . f|\mbox{~~}|<=>|\mbox{~~} |X `sse` f &&|~
\setlength{\jot}{-1pt}
\left(
 \begin{aligned}
 |do|~ & |a <- any| \\
       & |b0 <- X a| \\
       & |b1 <- f a| \\
       & |return (b0, b1)|
 \end{aligned}
 |`sse`|~~
 \begin{aligned}
 |do|~ & |(b0, b1) <- any| \\
       & |filt R (b0, b1)|
 \end{aligned}
 \right)
\end{equation*}

\bibliographystyle{jfplike}
\bibliography{monadic-opt.bib}
%\input{sublists.bbl}


\end{document}
