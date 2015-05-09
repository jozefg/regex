module Regex where
open import Data.Char                             using (Char;  _≟_)
open import Data.List                             using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary                      using (Dec; yes; no)
open import Data.Empty                            using (⊥)

open import Split

String : Set
String = List Char

data Regex : Set where
  any   : Regex
  both  : Regex → Regex → Regex
  then  : Regex → Regex → Regex
  or    : Regex → Regex → Regex
  char  : Char → Regex
  star  : Regex → Regex
  empty : Regex

data _∈_ : String → Regex → Set where
  any  : (c : Char) → (c ∷ []) ∈ any
  char : (c : Char) → (c ∷ []) ∈ char c
  or1  : (s : String)(r1 r2 : Regex)
       → s ∈ r1
       → s ∈ or r1 r2
  or2  : (s : String)(r1 r2 : Regex)
       → s ∈ r2
       → s ∈ or r1 r2
  both : (s : String)(r1 r2 : Regex)
       → s ∈ r1 → s ∈ r2
       → s ∈ both r1 r2
  then : (r₁ r₂ : Regex)(s s1 s2 : String)
       → Split.Split s s1 s2
       → s1 ∈ r₁
       → s2 ∈ r₂
       → s  ∈ then r₁ r₂
  starz : (r : Regex) → [] ∈ star r
  stars : (r : Regex)(s s1 s2 : String)
        → Split s s1 s2
        → s1 ∈ r
        → s2 ∈ star r
        → s ∈ star r

π₁ : {r r₂ : Regex}{s : String} → s ∈ both r r₂ → s ∈ r
π₁ (both s r1 r2 i i₁) = i

π₂ : {r r₂ : Regex}{s : String} → s ∈ both r r₂ → s ∈ r₂
π₂ (both s r1 r2 i i₁) = i₁

either : {r r₂ : Regex}{s : String}
       → (s ∈ r → ⊥) → (s ∈ r₂ → ⊥)
       → s ∈ or r r₂ → ⊥
either l r₁ (or1 s r r₂ p) = l p
either l r₁ (or2 s r r₂ p) = r₁ p

¬-char : {c c₁ : Char}{s : String} → c ≢ c₁ → (c ∷ s) ∈ char c₁ → ⊥
¬-char neq (char c) = neq refl

data StarR (r : Regex) : String → String → Set where
  rstar : (c : Char)(s₁ : String)(s₂ : String)
        → (c ∷ s₁) ∈ r → s₂ ∈ star r
        → StarR r (c ∷ s₁) s₂

srπ₁ : {r : Regex}{s₁ s₂ : String} → StarR r s₁ s₂ → s₁ ∈ r
srπ₁ (rstar c s₁ s₂ x x₁) = x

srπ₂ : {r : Regex}{s₁ s₂ : String} → StarR r s₁ s₂ → s₂ ∈ star r
srπ₂ (rstar c s₁ s₂ x x₁) = x₁

data ThenR (r₁ r₂ : Regex) (s₁ s₂ : String) : Set where
  rthen : s₁ ∈ r₁ → s₂ ∈ r₂ → ThenR r₁ r₂ s₁ s₂

trπ₁ : {r₁ r₂ : Regex}{s₁ s₂ : String} → ThenR r₁ r₂ s₁ s₂ → s₁ ∈ r₁
trπ₁ (rthen p _) = p

trπ₂ : {r₁ r₂ : Regex}{s₁ s₂ : String} → ThenR r₁ r₂ s₁ s₂ → s₂ ∈ r₂
trπ₂ (rthen _ p) = p

match : (s : String)(r : Regex) → Dec (s ∈ r)

{-# NO_TERMINATION_CHECK #-}
decStar : (r : Regex)(s s₁ s₂ : String)(sp : Split s s₁ s₂)
        → Dec (StarR r s₁ s₂)
decThen : (r₁ r₂ : Regex)(s s₁ s₂ : String)(sp : Split s s₁ s₂)
        → Dec (ThenR r₁ r₂ s₁ s₂)

decStar r s .[] .s (nil .s) = no (λ ())
decStar r .(c ∷ s) (.c ∷ s₁) s₂ (cons c s sp) with match (c ∷ s₁) r | match s₂ (star r)
decStar r .(c ∷ s) (.c ∷ s₁) s₂ (cons c s sp) | yes p | yes p₁ = yes (rstar c s₁ s₂ p p₁)
decStar r .(c ∷ s) (.c ∷ s₁) s₂ (cons c s sp) | yes p | no ¬p = no (λ p → ¬p (srπ₂ p))
decStar r .(c ∷ s) (.c ∷ s₁) s₂ (cons c s sp) | no ¬p | p' = no (λ p → ¬p (srπ₁ p))

decThen r₁ r₂ s s₁ s₂ sp with match s₁ r₁ | match s₂ r₂
decThen r₁ r₂ s s₁ s₂ sp | yes p | yes p₁ = yes (rthen p p₁)
decThen r₁ r₂ s s₁ s₂ sp | yes p | no ¬p = no (λ p → ¬p (trπ₂ p))
decThen r₁ r₂ s s₁ s₂ sp | no ¬p | yes p = no (λ p → ¬p (trπ₁ p))
decThen r₁ r₂ s s₁ s₂ sp | no ¬p | no ¬p₁ = no (λ p → ¬p (trπ₁ p))

match s (both r r₁) with match s r | match s r₁
match s (both r r₁) | yes p | yes p₁ = yes (both s r r₁ p p₁)
match s (both r r₁) | yes p | no ¬p  = no (λ p → ¬p (π₂ p))
match s (both r r₁) | no ¬p | yes p  = no (λ p → ¬p (π₁ p))
match s (both r r₁) | no ¬p | no ¬p₁ = no (λ p → ¬p (π₁ p))

match s (or r r₁) with match s r | match s r₁
match s (or r r₁) | yes p | yes p₁ = yes (or1 s r r₁ p)
match s (or r r₁) | yes p | no ¬p  = yes (or1 s r r₁ p)
match s (or r r₁) | no ¬p | yes p  = yes (or2 s r r₁ p)
match s (or r r₁) | no ¬p | no ¬p₁ = no (λ p → either ¬p ¬p₁ p)

match [] (char x) = no (λ ())
match (x ∷ s) (char x₁) with x ≟ x₁
match (x ∷ []) (char .x)     | yes refl = yes (char x)
match (x ∷ x₁ ∷ s) (char .x) | yes refl = no (λ ())
match (x ∷ s) (char x₁)      | no ¬     = no (λ p → ¬-char ¬ p)

match [] any = no (λ ())
match (x ∷ []) any = yes (any x)
match (x ∷ x₁ ∷ s) any = no (λ ())

match s empty = no (λ ())

match [] (star r) = yes (starz r)
match (x ∷ s) (star r) with decHasSplit (x ∷ s) (decStar r (x ∷ s))
match (x ∷ s) (star r) | yes (exists .(c ∷ s₁) s₂ sp (rstar c s₁ .s₂ x₁ x₂)) =
  yes (stars r (x ∷ s) (c ∷ s₁) s₂ sp x₁ x₂)
match (x ∷ s) (star r) | no ¬p = no contra
  where contra : (x ∷ s) ∈ star r → ⊥
        contra (stars .r .(x ∷ s) .[] .(x ∷ s) (nil ._) p p₁) = contra p₁
        contra (stars .r .(x ∷ s) (.x ∷ s₁) s2 (cons .x .s x₁) p p₁) =
          ¬p (exists (x ∷ s₁) s2 (cons x s x₁) (rstar x s₁ s2 p p₁))

match s (then r₁ r₂) with decHasSplit s (decThen r₁ r₂ s)
match s (then r₁ r₂) | yes (exists s₁ s₂ sp (rthen x x₁)) = yes (then r₁ r₂ s s₁ s₂ sp x x₁)
match s (then r₁ r₂) | no ¬p = no contra
  where contra : s ∈ then r₁ r₂ → ⊥
        contra (then .r₁ .r₂ .s s1 s2 x p p₁) = ¬p (exists s1 s2 x (rthen p p₁))

import Data.String as S

check : (s : S.String)(r : Regex) → Dec (S.toList s ∈ r)
check s r = match (S.toList s) r
