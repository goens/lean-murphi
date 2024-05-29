-- Utility:
def Monad.kleisliLeftToRight {A B C : Type} [Monad M] : (A → M B) → (B → M C) → A → M C
 | f₁, f₂, a => do
   let b <- f₁ a
   f₂ b

infixl:55 " >=> "  => Monad.kleisliLeftToRight
