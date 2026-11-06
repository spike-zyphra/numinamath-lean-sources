import Mathlib

open Finset

/-
On an infinite checkerboard, two players alternately mark one unmarked cell. One of them uses $\times$, the other $o$. The first who fills a $2 \times 2$ square with his symbols wins. Can the player who starts always win?
-/
theorem combinatorics_239111 (a : ℕ → ℕ → ℕ)
    (ha : ∀ i j, a i j = if i % 2 = j % 2 then 1 else 0) :
    ¬∃ i j, a i j = 1 ∧ a (i + 1) j = 1 ∧ a i (j + 1) = 1 ∧ a (i + 1) (j + 1) = 1 := by

  -- Assume, for the sake of contradiction, that such a 2×2 square exists
  rintro ⟨i, j, h₁, h₂, h₃, h₄⟩
  
  -- Apply the given condition to each cell in the 2×2 square
  have h₅ : a i j = if i % 2 = j % 2 then 1 else 0 := ha i j
  have h₆ : a (i + 1) j = if (i + 1) % 2 = j % 2 then 1 else 0 := ha (i + 1) j
  have h₇ : a i (j + 1) = if i % 2 = (j + 1) % 2 then 1 else 0 := ha i (j + 1)
  have h₈ : a (i + 1) (j + 1) = if (i + 1) % 2 = (j + 1) % 2 then 1 else 0 := ha (i + 1) (j + 1)
  
  -- Rewrite the assumptions using the parity conditions
  rw [h₅] at h₁
  rw [h₆] at h₂
  rw [h₇] at h₃
  rw [h₈] at h₄
  
  -- Split each conditional statement into cases based on parity
  split_ifs at h₁ h₂ h₃ h₄ 
  
  omega