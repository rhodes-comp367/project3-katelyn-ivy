open import Agda.Builtin.Equality
  using (_≡_; refl)
open import Agda.Builtin.Nat
  using (Nat; _+_; _*_; suc; zero)
open import Agda.Builtin.Bool 

-- # Misc. Definitions + Functions

data ⊥ : Set where

~ : Set → Set
~ P = P → ⊥

data T : Bool → Set where
  tt : T true

data _⊔_ (A B : Set) : Set where
  left : A → A ⊔ B
  right : B → A ⊔ B
infix 3 _⊔_

data _<_ : Nat → Nat → Set where
  zero : ∀ {b}
    → zero < suc b
  suc : ∀ {a b} → a < b
    → suc a < suc b
infix 4 _<_

-- Decidable equality (for <?) builtin style
data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : (P → ⊥) → Dec P

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()

-- ## Definitions : Basic List

data List (A : Set) : Set where
    [] : List A
    _,_ : A → List A → List A
infixr 20 _,_ 

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
  T (contains n (concat xs ys)) → T (contains n xs) ⊔ T (contains n ys) -- i.e. if an element is in concat (xs ys), then it was
contains-concat n [] ys p = right p                                     -- originally in either xs or ys
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

-- Slist inspired by mazzo.li (website).
-- Optional: figure out how to set upper lower bounds to 1 - 10 always
data SList (l u : Nat) : Set where
  nil : l < u → SList l u 
  cons : (x : Nat) → SList x u → l < x → SList l u

-- Converts Sorted List to normal list to improve readability.
toList : ∀ {l u} → SList l u → List Nat
toList (nil _) = []
toList (cons x xs _) = (x , toList xs)

-- Helper function for insert: decidable inequality.
-- Based on decidable equality function. Using Dec type for cleaner implementation.
_<?_ : ∀ (x y : Nat) → Dec (x < y)
zero  <? zero   = no (λ ())
zero  <? suc y  = yes zero
suc x <? zero   = no (λ ())
suc x <? suc y  with x <? y
... | yes x<y = yes (suc x<y)
... | no ¬x<y = no (λ { (suc x<y) → ¬x<y x<y })

-- Helper function for insert: converts "not less than" to "greater than or equal to"
-- Created with help from DeepSeek.
≮-implies-> : ∀ {x y} → ~ (y < x) → x < y ⊔ x ≡ y
≮-implies-> {zero} {zero} _ = right refl
≮-implies-> {zero} {suc y} ¬x<y = left zero  -- zero < suc y is always true
≮-implies-> {suc x} {zero} ¬y<x = ⊥-elim (¬y<x zero)  -- suc x > zero is always true
≮-implies-> {suc x} {suc y} ¬x<y with ≮-implies-> (λ x<y → ¬x<y (suc x<y))
... | left y<x = left (suc y<x)
... | right refl = right refl

-- inspired by mazzo.li (website).
insert : ∀ {l u} x → SList l u → l < x → x < u → SList l u
insert x (nil l<u) l<x x<u = cons x (nil x<u) l<x
insert x (cons y ys l<y) l<x x<u with x <? y
... | yes x<y = cons x (cons y ys x<y) l<x
... | no ¬x<y with ≮-implies-> ¬x<y
...   | left y<x = cons y (insert x ys y<x x<u) l<y
...   | right refl = cons y ys l<y  -- x ≡ y, duplicate, just return original

merge' : ∀ {l u} → (n : Nat) → SList l u → SList l u → SList l u
merge' zero xs ys = xs  -- fallback
merge' (suc n) xs (nil _) = xs
merge' (suc n) (nil _) (cons y ys l<y) = (cons y ys l<y)
merge' (suc n) (cons x xs l<x) (cons y ys l<y) with x <? y
... | yes x<y = cons x (merge' n xs (cons y ys x<y)) l<x
... | no ¬x<y with ≮-implies-> ¬x<y
...   | left y<x = cons y (merge' n (cons x xs y<x) ys) l<y
...   | right refl = cons x (merge' n xs ys) l<x


Scontains : ∀ {l u} → Nat → SList l u → Bool
Scontains n (nil _) = false 
Scontains n (cons x xs l<x) with nat-dec n x
... | left _ = true
... | right _ = Scontains n xs 

Ssize : ∀ {l u} → SList l u → Nat
Ssize (nil _) = zero
Ssize (cons x xs l<x) = suc (Ssize xs)

-- ## Proofs 

-- After inserting an element n into an Slist, the list's size will either remain the same or increase by 1.
insert-size : ∀ {l u} → (n : Nat) → (xs : SList l u) → (l<n : l < n) → (n<u : n < u) →
              (Ssize (insert n xs l<n n<u) ≡ Ssize xs) ⊔ (Ssize (insert n xs l<n n<u) ≡ suc (Ssize xs))
insert-size n (nil _) _ _ = right refl  -- inserting into an empty list increases the size by 1
insert-size n (cons x xs _) l<n n<u with n <? x
... | yes _ = right refl -- n < x, therefore size increases by 1
... | no ¬n<x with ≮-implies-> ¬n<x  
...   | right refl = left refl -- n ≡ x, therefore size remains the same
...   | left x<n with insert-size n xs x<n n<u -- x < n; insert n into xs using recursive case 
...     | left rec rewrite rec = left refl -- size remains the same
...     | right rec rewrite rec = right refl -- size increases by 1

-- Inserting n into an empty SList returns n.
insert-into-empty : ∀ {l u} (n : Nat) (l<u : l < u) (l<n : l < n) (n<u : n < u) →
  insert n (nil l<u) l<n n<u ≡ cons n (nil n<u) l<n
insert-into-empty n l<u l<n n<u = refl



