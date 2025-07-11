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


\counterwithout{equation}{section}


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
One therefore needs a different framework, where a specification describes a collection of solution that is allowed by the final program, which no longer equals the specification, but is rather contained by the latter.

One of the possibilities is to use relations as specifications.
Foundations of this approach were laid by works including \cite{BackhousedeBruin:91:Relational}, \cite{Aarts:92:Relational}, \cite{BackhouseHoogendijk:92:Elements}, etc,
before \cite{BirddeMoor:97:Algebra},
which took a even more abstract, categorical approach,
presented general theories for constructing various forms of greedy, thinning, and dynamic programming algorithms.
\cite{BirddeMoor:97:Algebra} presented a point-free calculus that is concise, elegant, and surprisingly expressive.
Such conciseness and expressiveness also turned out to be a curse, however.
For those who not sharing the background, the calculus has a sharp learning curve, which limited its popularity to a small circle of enthusiasts.

\cite{deMoorGibbons:00:Pointwise}
\cite{BirdRabe:19:How}
\cite{BirdGibbons:20:Algorithm}

\bibliographystyle{jfplike}
\bibliography{monadic-opt.bib}
%\input{sublists.bbl}


\end{document}
