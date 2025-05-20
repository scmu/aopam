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

%% lhs2Tex mss.lhs | pdflatex --jobname=mss

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

max :: P (List Int) -> P (List Int)
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

leqs :: List Int -> List Int -> Bool
leqs xs ys = sum xs <= sum ys

geqs :: List Int -> List Int -> Bool
geqs xs ys = sum xs >= sum ys

\end{code}
%endif

%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
%include exists.fmt

%include common/Formatting.fmt
%include common/Relation.fmt

%%\email{scm@iis.sinica.edu.tw}

%format `leqs` = "\mathrel{\leq_{s}}"
%format `geqs` = "\mathrel{\geq_{s}}"

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

\title{Maximum Segment Sum in a Monadic Setting}

\author{\color{black}Shin-Cheng Mu}
\date{%
Institute of Information Science, Academia Sinica
}

\maketitle


\section{Definitions}

An monadic variation of |foldr| is defined by:
\begin{code}
foldR :: (a -> b -> P b) -> P b -> List a -> P b
foldR f e []        = e
foldR f e (x : xs)  = f x =<< foldR f e xs {-"~~."-}
\end{code}
The function |foldR| can be defined using ordinary |fold| --- we have |foldR f e =| |foldr (\x m -> f x =<< m) e|.
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
Due to the way we define our |foldR|,
the equivalence of the two definitions of |prefix| depends on
idempotency of the non-determinism monad --- the second definition returns |[]| more frequently.

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

\section{Elementary Properties}

The function |max| distributes into |join|:
%if False
\begin{code}
-- propMaxJoin :: forall {k} (a :: Type). P (P a) -> P a
propMaxJoin xss = max (join xss) === max (join (fmap max xss))
\end{code}
%endif
\begin{equation}
  |max (join xss) === max (join (fmap max xss))| \mbox{~~.}
   \label{eq:MaxJoin}
\end{equation}
I hope this property can be proved using more primitive properties.

With \eqref{eq:MaxJoin} we know how |max| promotes into a bind or a Kliesli composition:
\begin{equation}
  |max (f <=< g) === max ((max . f) <=< g)| \mbox{~~.}
   \label{eq:MaxKComp}
\end{equation}
The proof goes:
%if False
\begin{code}
-- propMaxJoin :: forall {k} (a :: Type). P (P a) -> P a
propMaxBind f g xs =
\end{code}
%endif
\begin{code}
      max (f =<< g xs)
 ===    {- definition of |(=<<)| -}
      max (join (fmap f (g xs)))
 ===    {- \eqref{eq:MaxJoin} -}
      max (join (fmap (max . f) (g xs)))
 ===    {- definition of |(=<<)| -}
      max ((max . f) =<< g xs) {-"~~."-}
\end{code}

The function |member| non-deterministically returns an element of the given list.
Put it in another way, it converts a list to a set:
\begin{code}
member :: List a -> P a
member []        = mzero
member (x : xs)  = return x <|> member xs {-"~~."-}
\end{code}

Monadic |max| can be refined to operate on lists
\begin{equation}
 |max . member `spse` return . maxlist| \label{eq:MaxMaxList}
\end{equation}
where |maxlist| is some implementation of maximum on lists.


\section{Properties of fold and scan}

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

\section{The Main Derivation}

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
TODO: Gotta think about what basic laws we need to allow the proof above to go through.

\end{document}
