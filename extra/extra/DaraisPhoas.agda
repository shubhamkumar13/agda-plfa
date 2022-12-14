module DaraisPhoas where

open import Agda.Primitive using (_โ_)

module Prelude where

  infixr 3 โ๐ ๐ก
  infixl 5 _โจ_
  infixr 20 _โท_

  data ๐น : Set where
    T : ๐น
    F : ๐น

  data _โจ_ {โโ โโ} (A : Set โโ) (B : Set โโ) : Set (โโ โ โโ) where
    Inl : A โ A โจ B
    Inr : B โ A โจ B

  syntax โ๐ ๐ก A (ฮป x โ B) = โ x โฆ A ๐ ๐ก B
  data โ๐ ๐ก {โโ โโ} (A : Set โโ) (B : A โ Set โโ) : Set (โโ โ โโ) where
    โจโ_,_โฉ : โ (x : A) โ B x โ โ x โฆ A ๐ ๐ก B x

  data โฌ_โญ {โ} (A : Set โ) : Set โ where
    [] : โฌ A โญ
    _โท_ : A โ โฌ A โญ โ โฌ A โญ

open Prelude

infixr 15 _โจโโฉ_
data type : Set where
  โจโโฉ   : type
  _โจโโฉ_ : type โ type โ type

infixl 15 _โจโโฉ_
data exp-phoas (var : type โ โฌ type โญ โ Set) : โ (ฮ : โฌ type โญ) (ฯ : type) โ Set where
  Var : โ {ฮ ฯ}
    (x : var ฯ ฮ)
    โ exp-phoas var ฮ ฯ
  โจฮปโฉ : โ {ฮ ฯโ ฯโ}
    (e : var ฯโ (ฯโ โท ฮ) โ exp-phoas var (ฯโ โท ฮ) ฯโ)
    โ exp-phoas var ฮ (ฯโ โจโโฉ ฯโ)
  _โจโโฉ_ : โ {ฮ ฯโ ฯโ}
    (eโ : exp-phoas var ฮ (ฯโ โจโโฉ ฯโ))
    (eโ : exp-phoas var ฮ ฯโ)
    โ exp-phoas var ฮ ฯโ

infix 10 _โ_
data _โ_ {โ} {A : Set โ} (x : A) : โ (xs : โฌ A โญ) โ Set โ where
  Z : โ {xs} โ x โ x โท xs
  S : โ {xโฒ xs} โ x โ xs โ x โ xโฒ โท xs

infix 10 _โข_
data _โข_ : โ (ฮ : โฌ type โญ) (ฯ : type) โ Set where
  Var : โ {ฮ ฯ}
    (x : ฯ โ ฮ)
    โ ฮ โข ฯ
  โจฮปโฉ : โ {ฮ ฯโ ฯโ}
    (e : ฯโ โท ฮ โข ฯโ)
    โ ฮ โข ฯโ โจโโฉ ฯโ
  _โจโโฉ_ : โ {ฮ ฯโ ฯโ}
    (eโ : ฮ โข ฯโ โจโโฉ ฯโ)
    (eโ : ฮ โข ฯโ)
    โ ฮ โข ฯโ

โฆ_โงโ : โ {ฮ ฯ} (e : exp-phoas _โ_ ฮ ฯ) โ ฮ โข ฯ
โฆ Var x โงโ = Var x
โฆ โจฮปโฉ e โงโ = โจฮปโฉ โฆ e Z โงโ
โฆ eโ โจโโฉ eโ โงโ = โฆ eโ โงโ โจโโฉ โฆ eโ โงโ

โฆ_โงโ : โ {ฮ ฯ} (e : ฮ โข ฯ) โ exp-phoas _โ_ ฮ ฯ
โฆ Var x โงโ = Var x
โฆ โจฮปโฉ e โงโ = โจฮปโฉ (ฮป _ โ โฆ e โงโ)
โฆ eโ โจโโฉ eโ โงโ = โฆ eโ โงโ โจโโฉ โฆ eโ โงโ

Ch : type
Ch =  (โจโโฉ โจโโฉ โจโโฉ) โจโโฉ โจโโฉ โจโโฉ โจโโฉ

twoDB : [] โข Ch
twoDB = โจฮปโฉ (โจฮปโฉ (Var (S Z) โจโโฉ (Var (S Z) โจโโฉ Var Z)))

twoPH : exp-phoas _โ_ [] Ch
twoPH = โจฮปโฉ (ฮป f โ โจฮปโฉ (ฮป x โ Var f โจโโฉ (Var f โจโโฉ Var x)))

{-
/Users/wadler/sf/src/extra/DaraisPhoas.agda:82,9-60
โจโโฉ โจโโฉ โจโโฉ != โจโโฉ of type type
when checking that the expression
โจฮปโฉ (ฮป f โ โจฮปโฉ (ฮป x โ Var f โจโโฉ (Var f โจโโฉ Var x))) has type
exp-phoas _โ_ [] Ch
-}
