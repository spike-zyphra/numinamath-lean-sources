import Mathlib

open Nat

/--
The theorem states:
  1. 5 * 7 divides x(2, 4), so x₅ is divisible by 35 when a = 2.
  2. For any a < 2, 5 * 7 does NOT divide x(a, 4).  (The only smaller a > 0 is a = 1, which fails.)
Hence 2 is the minimal positive integer a with 35 ∣ x(a, 4).
-/
theorem minimal_x₁ ( x : ℕ → ℕ → ℕ)(hx0:∀a,x a 0=a)(hx1:∀ a,x a 1=a^2)(hx3:∀n a,x a (n+2)=(x a (n+1)*((x a (n+1))+1)))(P₁:ℕ)(hp1:P₁=5)(P₂:ℕ)(hp2:P₂=7):
  (P₁ * P₂) ∣ x 2 4 ∧ ∀ a, 0 < a ∧ a < 2 → ¬ ((P₁ * P₂) ∣ x a 4) := by
  -- 1) Show 35 ∣ x(2, 4).
  have : x 2 4 = (x 2 3) * (x 2 3 + 1) :=by let r:=(hx3 2 2);simp at r;exact r
  -- We compute the first few values:
  --   x(2, 0) = 2
  --   x(2, 1) = 2^2 = 4
  --   x(2, 2) = 4 * (4 + 1) = 20
  --   x(2, 3) = 20 * 21 = 420
  --   x(2, 4) = 420 * 421
  have h₀ : x 2 0 = 2 :=by exact (hx0 2)
  have h₁ : x 2 1 = 4 := by exact (hx1 2)
  have h₂ : x 2 2 = 20 := by let r:=hx3 0 2;simp[h₁] at r;exact r
  have h₃ : x 2 3 = 420 := by let r:=hx3 1 2;simp[h₂] at r;exact r
  have h₄ : x 2 4 = 420 * 421 := by let r:=hx3 2 2;simp[h₃] at r;exact r
  have hx35 : (5 * 7) ∣ (420 : ℕ) := by
    -- 420 = 60 * 7 = (12 * 5) * 7
    show 35 ∣ 420
    norm_num            -- 420 is clearly divisible by 35
  -- Since 420 ≡ 0 mod 35, also 420 * 421 ≡ 0 mod 35:
  have part1 : (P₁ * P₂) ∣ x 2 4 := by
    rw [hp1, hp2];
    rw [h₄];
    trivial

  -- 2) Show that for a = 1, 35 ∤ x(1, 4), and hence for all a < 2, it fails.
  have h1 : x 1 0 = 1 := by exact (hx0 1)
  have h1' : x 1 1 = 1 :=by exact (hx1 1)
  have h1'' : x 1 2 = 2 := by let r:=hx3 0 1;simp[h1'] at r;exact r
  have h1₃ : x 1 3 = 6 :=  by let r:=hx3 1 1;simp[h1''] at r;exact r
  have h1₄ : x 1 4 = 42 :=  by let r:=hx3 2 1;simp[h1₃] at r;exact r
  have n35_1 : ¬ 35 ∣ 42 := by
    -- 42 mod 35 = 7 ≠ 0
    norm_num

  have part2 : ∀ a, 0 < a ∧ a < 2 → ¬ ((P₁ * P₂) ∣ x a 4) := by
    intro a ⟨hpos, hlt⟩
    -- Since 0 < a < 2, we have a = 1
    interval_cases a
    rw[h1₄,hp1,hp2]
    trivial

  exact ⟨part1, part2⟩