postulate String : Set

data Basic : Set where
  A : Basic
  B : Basic
  C : Basic

data Type : Set where
  Unit : Type
  Times : Type → Type → Type
  Arrow : Type → Type → Type
  Name : Basic → Type

data Ctx : Set where
  [] : Ctx
  _∷_ : Type → Ctx → Ctx

data _⊢_ : Ctx → Type → Set where
  
  -- Unit
  Ast : {Γ : Ctx} → Γ ⊢ Unit
  
  -- Product
  Prod : {Γ : Ctx}{A B : Type}
    → Γ ⊢ A
    → Γ ⊢ B
    → Γ ⊢ Times A B

  Pi1 : {Γ : Ctx}{A B : Type}
    → Γ ⊢ Times A B
    → Γ ⊢ A

  Pi2 : {Γ : Ctx}{A B : Type}
    → Γ ⊢ Times A B
    → Γ ⊢ B


  -- Arrow
  
  
