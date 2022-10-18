data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (n O) = n I
inc (n I) = (inc n) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (n O) = 2 * (from n)
from (n I) = suc (2 * (from n))

inc-example : inc (((((((⟨⟩ I) I) O) O) I) O) O) ≡ (((((((⟨⟩ I) I) O) O) I) O) I)
inc-example = refl

to-example : to 1 ≡ ⟨⟩ I
to-example = refl
