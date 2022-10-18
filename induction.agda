import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p  = refl

+-identity : ∀ (n : ℕ) → n + zero ≡ n
+-identity zero = refl
+-identity (suc n) rewrite +-identity n = refl

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n rewrite +-suc m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero rewrite +-identity m = refl
+-comm m (suc n) rewrite +-suc m n | +-comm m n = refl

+-assoc-rev : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
+-assoc-rev zero n p = refl
+-assoc-rev (suc m) n p rewrite +-assoc m n p = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap zero n p = refl
+-swap (suc m) n p rewrite +-suc n (m + p) | +-swap m n p = refl

*-idempotence : ∀ (n : ℕ) → n * zero ≡ zero
*-idempotence zero = refl
*-idempotence (suc n) rewrite *-idempotence n = refl

*-identity : ∀ (n : ℕ) → n * (suc zero) ≡ n
*-identity zero = refl
*-identity (suc n) rewrite *-identity n = refl

-- *-suc : ∀ (m n : ℕ) → m * suc n ≡ m * n + m
-- *-suc zero n = refl
-- *-suc (suc m) n rewrite *-suc m n with (m * n)
-- ...                               | r rewrite +-assoc-rev n r m with (n + r)
-- ...                                                             | x rewrite +-suc x m = refl

+-dumb : ∀ (a b c : ℕ) → a + (b + c) ≡ a + b + c
+-dumb zero b c = refl
+-dumb (suc a) b c rewrite +-dumb a b c = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-identity p | *-distrib-+ m n p | +-dumb p (m * p) (n * p) = refl

*-dumb : ∀ (a b c : ℕ) → a * (b * c) ≡ a * b * c
*-dumb zero b c = refl
*-dumb (suc a) b c rewrite *-dumb a b c | *-distrib-+ b (a * b) c = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-assoc m n p | *-distrib-+ n (m * n) p | *-dumb m n p = refl
