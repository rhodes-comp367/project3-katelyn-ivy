open import Agda.Builtin.Equality
  using (_≡_; refl)
open import Agda.Builtin.Nat
  using (Nat; _+_; _*_; suc; zero)
open import Agda.Builtin.Bool 

-- # Misc. Definitions

data ⊥ : Set where

~ : Set → Set
~ P = P → ⊥

data T : Bool → Set where
  tt : T true

data _⊔_ (A B : Set) : Set where
  left : A → A ⊔ B
  right : B → A ⊔ B
infix 3 _⊔_


-- ## Definitions : Basic List

data List (A : Set) : Set where
    [] : List A
    _,_ : A → List A → List A

concat : {A : Set} → List A → List A → List A
concat [] ys = ys
concat (x , xs) ys = x , (concat xs ys)

prepend : {A : Set} → A → List A → List A
prepend x ys = x , ys

reverse : List Nat → List Nat
reverse [] = []
reverse (x , xs) = concat (reverse xs) (x , [])

-- helper function taken from Equal.Agda
-- natural number equality is decidable.
nat-dec : (m n : Nat) → m ≡ n ⊔ ~ (m ≡ n)
nat-dec zero zero = left refl
nat-dec zero (suc _) = right (λ ())
nat-dec (suc _) zero = right (λ ())
nat-dec (suc m) (suc n) with nat-dec m n
... | left refl = left refl
... | right p = right (λ {refl → p refl})

contains : Nat → List Nat → Bool
contains n [] = false
contains n (x , xs) with nat-dec n x 
... | left _  = true  
... | right _ = contains n xs  

size : {A : Set} → List A → Nat
size [] = zero 
size (x , xs) = suc (size xs) 

-- ## Proofs

-- concatenating an empty list to another list results in no change. 
concat-empty : (xs : List Nat) → (concat [] xs) ≡ xs
concat-empty xs = refl

-- concatenating empty list proof (right side)
concat-empty-right : (xs : List Nat) → (concat xs []) ≡ xs
concat-empty-right [] = refl
concat-empty-right (x , xs) rewrite concat-empty-right xs = refl

-- concatenation adds the sizes of the two lists together.
concat-size : (xs ys : List Nat) → size (concat xs ys) ≡ size xs + size ys
concat-size [] ys rewrite concat-empty ys = refl
concat-size (x , xs) ys rewrite concat-size xs ys = refl

-- concatenation preserves list elements.
contains-concat : (n : Nat) (xs ys : List Nat) →
  T (contains n (concat xs ys)) → T (contains n xs) ⊔ T (contains n ys)
contains-concat n [] ys p = right p
contains-concat n (x , xs) ys p with nat-dec n x 
... | left refl = left tt
... | right f = contains-concat n xs ys p
    
-- concat is associative. 
concat-assoc : (xs ys zs : List Nat) → (concat (concat xs ys) zs) ≡ (concat xs (concat ys zs))
concat-assoc [] ys zs = refl
concat-assoc (x , xs) ys zs rewrite concat-assoc xs ys zs = refl

-- helper function for rev-size; created with help from DeepSeek.
+-suc : (n : Nat) → n + 1 ≡ suc n
+-suc zero = refl
+-suc (suc n) rewrite +-suc n = refl

-- reversing a list preserves size.
rev-size : (xs : List Nat) → size (reverse xs) ≡ size xs
rev-size [] = refl
rev-size (x , xs) rewrite concat-size (reverse xs) (x , [])
  | rev-size xs 
  | +-suc (size xs) = refl 

-- reverse is distributive. 
rev-dist : (xs ys : List Nat) → reverse (concat xs ys) ≡ concat (reverse ys) (reverse xs) 
rev-dist [] ys rewrite concat-empty ys 
  | concat-empty-right (reverse ys) = refl
rev-dist (x , xs) [] rewrite concat-empty-right xs = refl
rev-dist (x , xs) (y , ys) rewrite rev-dist xs (y , ys) 
  | concat-assoc (reverse (y , ys)) (reverse xs) (x , []) = refl

-- reversing a list twice results in no change.
rev-involutive : (xs : List Nat) → (reverse (reverse xs)) ≡ xs
rev-involutive [] = refl
rev-involutive (x , xs)
  rewrite rev-dist (reverse xs) (x , [])
  | rev-involutive xs = refl


-- ## Definitions: Sorted List