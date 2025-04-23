open import Agda.Builtin.Equality
  using (_≡_; refl)
open import Agda.Builtin.Nat
  using (Nat; _+_; _*_; suc; zero)
open import Agda.Builtin.Bool


data List (A : Set) : Set where
    [] : List A
    _,_ : A → List A → List A

concat : {A : Set} → List A → List A → List A
concat [] ys = ys
concat (x , xs) ys = x , (concat xs ys)

prepend : {A : Set} → A → List A → List A
prepend x ys = x , ys

contains : {A : Set} → A → List A → Bool
contains n [] = false
contains n (x , xs) = {!   !}
