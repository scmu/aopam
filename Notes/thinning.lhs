\documentclass[dvipsnames, fleqn, 11pt]{article}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{natbib}

\usepackage{classicthesis}

\linespread{1.05} % a bit more for Palatino
\areaset[current]{420pt}{761pt} % 686 (factor 2.2) + 33 head + 42 head \the\footskip
\setlength{\marginparwidth}{7em}%
\setlength{\marginparsep}{2em}%

\usepackage{url}
\let\Bbbk\relax  % avoiding error "Bbbk' already defined."
\usepackage{tikz}
\usepackage{chngcntr} % for \counterwithout
\usepackage{caption}
\usepackage{subcaption}
\usepackage{scalerel}

%% lhs2Tex thinning.lhs | pdflatex --jobname=thinning

%if False
\begin{code}
{-# OPTIONS_GHC -Wno-missing-methods #-}
import Prelude hiding (max, any)
import GHC.Base (Alternative)
import Data.Kind (Type)
import Control.Applicative
import Control.Monad

(===) :: a -> a -> a
(===) = undefined

infixr 0 ===

-- type P a = [a]
data P a

instance Functor P where
instance Applicative P where
instance Monad P where
instance Alternative P where
instance MonadPlus P where
instance MonadFail P where

type List a = [a]

max :: P a -> P a
max = undefined

maxlist :: List a -> a
maxlist = undefined

any :: P a
any = undefined

infixr 0 `spse`
spse :: a -> a -> a
spse = undefined

infixr 0 `sse`
sse :: a -> a -> a
sse = undefined

wrap x = [x]

data T a

instance Functor T where
-- instance Applicative T where
-- instance Monad T where
-- instance Alternative T where
-- instance MonadPlus T where
-- instance MonadFail T where

thin_Q :: T a -> P (T a)
thin_Q = undefined

collect :: P a -> T a
collect = undefined

mem :: T a -> P a
mem = undefined

filt_Q :: (a, a) -> P (a, a)
filt_Q = undefined
\end{code}
%endif

%format filt_Q = "\mathit{filt}_{\mathit{Q}}"

%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include exists.fmt

%include common/Formatting.fmt
%include common/Relation.fmt

%%\email{scm@iis.sinica.edu.tw}

\usepackage{common/doubleequals}

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}

%\def\commentbegin{\quad$\{$~}
%\def\commentend{$\}$}
\def\commentbegin{\quad\begingroup\color{SeaGreen}\{\ }
\def\commentend{\}\endgroup}

\mathindent=\parindent
\addtolength{\mathindent}{0.3cm}

\definecolor{mediumpersianblue}{rgb}{0.0, 0.4, 0.65}
\everymath{\color{mediumpersianblue}}
\apptocmd{\[}{\color{mediumpersianblue}}{}{}
\AtBeginEnvironment{equation}{\color{mediumpersianblue}}
\AtBeginEnvironment{equation*}{\color{mediumpersianblue}}

\allowdisplaybreaks

\newcommand{\tagx}[1][]{\refstepcounter{equation}(\theequation)\label{#1}}
\newcommand\numberthis{\refstepcounter{equation}\tag{\theequation}}


\counterwithout{equation}{section}

\begin{document}

\title{Various Formulation of the Greedy Theorem and Their Proofs}

\author{\color{black}Shin-Cheng Mu}
\date{%
Institute of Information Science, Academia Sinica
}

\maketitle


\section{Relation, Thinning, Fixed-Point}

%{
%format R = "\Varid{R}"
%format Q = "\Varid{Q}"
%format S = "\Varid{S}"
%format X = "\Varid{X}"

Recall the fixed-point properties of catamorphism:
\begin{spec}
 cata R `sse` X {-"~"-}<=={-"~"-} R . F X . conv alpha `sse` X  {-"~~,"-}
 X `sse` cata R {-"~"-}<=={-"~"-} X `sse` R . F X . conv alpha  {-"~~."-}
\end{spec}
The relation |thin| is defined by
\begin{spec}
  thin_Q = (mem `lfac` mem) `cap` ((ni . Q){-"\!"-}/{-"\!"-}ni ){-"~~,"-}
\end{spec}
with the universal property
\begin{spec}
  X `sse` thin_Q . Lam S {-"~\,"-}<=>{-"~\,"-} mem . X `sse` S {-"\,"-}&& {-"\,"-} X . conv S `sse` ni . R {-"~~."-}
\end{spec}
In particular, letting |X = thin_Q . Lam S| we have |thin_Q . Lam S . conv S `sse` ni . Q|.

The thinning theorem is given by
\begin{spec}
  thin_Q . Lam (cata S) {-"\,"-}`spse` {-"\,"-} cata (thin_Q . Lam (S . F mem)) {-"~"-}<=={-"~"-} F Q . conv S `sse` conv S . Q {-"~~."-}
\end{spec}
\begin{proof}
As in the case with |min|, we choose the route which does not use hylomorphism.
By the fixed-point property of catamorphism:
\begin{spec}
     cata (thin_Q . Lam (S . F mem)) `sse` thin_Q . Lam (cata S)
<==    {- fixed-point property of cata -}
     thin_Q . Lam (S . F mem) . F (thin_Q . Lam (cata S)) . conv alpha `sse` thin_Q . Lam (cata S)
<=>    {- universal property of |thin| -}
     mem . thin_Q . Lam (S . F mem) . F (thin_Q . Lam (cata S)) . conv alpha `sse` cata S &&
     thin_Q . Lam (S . F mem) . F (thin_Q . Lam (cata S)) . conv alpha . conv (cata S) `sse` ni . Q {-"~~."-}
\end{spec}
For the first clause, we reason:
\begin{spec}
     mem . thin_Q . Lam (S . F mem) . F (thin_Q . Lam (cata S)) . conv alpha
`sse`   {- |mem . thin_Q `sse` mem| -}
     mem . Lam (S . F mem) . F (thin_Q . Lam (cata S)) . conv alpha
`sse`   {- |mem . Lam R `sse` R| -}
     S . F (mem . thin_Q . Lam (cata S)) . conv alpha
`sse`   {- |mem . thin_Q `sse` mem| -}
     S . F (mem . Lam (cata S)) . conv alpha
`sse`   {- |mem . Lam R `sse` R| -}
     S . F (cata S) . conv alpha
=       {- catamorphism -}
     cata S {-"~~."-}
\end{spec}

Regarding the second clause:
\begin{spec}
       thin_Q . Lam (S . F mem) . F (thin_Q . Lam (cata S)) . conv alpha . conv (cata S)
=       {- catamorphism -}
       thin_Q . Lam (S . F mem) . F (thin_Q . Lam (cata S)) . F (conv (cata S)) . conv S
`sse`   {- |thin_Q . Lam R . conv R `sse` ni . Q| -}
       thin_Q . Lam (S . F mem) . F (ni . Q) . conv S
`sse`   {- |F Q . conv S `sse` conv S . Q| -}
       thin_Q . Lam (S . F mem) . F ni . conv S . Q
`sse`   {- |thin_Q . Lam R . conv R `sse` ni . Q| -}
       ni . Q . Q
`sse`   {- |Q| transitive -}
       Q {-"~~."-}
\end{spec}
\end{proof}
%}


\section{Monad, Minimum, Lists}

%{
%format X = "\Varid{X}"
%format b0
%format b1
%format b2
%format y0
%format y1
%format t0
%format u0

Recall the monadic |foldr|:
\begin{code}
foldR :: (a -> b -> P b) -> P b -> List a -> P b
foldR f e []        = e
foldR f e (x : xs)  = f x =<< foldR f e xs {-"~~."-}
\end{code}
with the following properties
\begin{spec}
foldR f e `sse` X {-"~"-}<=={-"~"-} e `sse` X [] {-"\,"-}&&{-"\,"-} f x =<< X xs `sse` X (x:xs)  {-"~~,"-}
X `sse` foldR f e {-"~"-}<=={-"~"-} X [] `sse` e {-"\,"-}&&{-"\,"-} X (x:xs) `sse` f x =<< X xs  {-"~~."-}
\end{spec}

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

}

\end{document}
