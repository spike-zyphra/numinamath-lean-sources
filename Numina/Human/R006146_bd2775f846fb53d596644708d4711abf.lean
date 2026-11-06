import Mathlib

open Finset

/-Positive integers $a$, $b$, $c$, $d$ satisfy $a>b>c>d$, $a+b+c+d=2010$, and $a^2-b^2+c^2-d^2=2010$. How many different possible values of $(a,b,c,d)$ are there?-/
theorem algebra_623595 : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a > b ∧ b > c ∧ c > d ∧ d > 0
    ∧ a + b + c + d = 2010 ∧ a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2 = 2010}.ncard = 501 := by
-- Define $f$ to be a function from ℕ × ℕ to ℕ × ℕ × ℕ × ℕ of the following form
  let f : ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun (b, d) => (b + 1, b, d + 1, d)
-- Prove that the set in question is an image of certain finite set under $f$
  have fimg : image f {p ∈ (Icc 1 1004) ×ˢ (Icc 1 1004) | p.1 > p.2
  ∧ p.1 + p.2 = 1004} = {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a > b ∧ b > c ∧ c > d ∧ d > 0
    ∧ a + b + c + d = 2010 ∧ a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2 = 2010} := by
    simp [Set.ext_iff, f, and_assoc]; intro a b c d; constructor
    · rintro ⟨x, xge, xle, y, yle, yge, yltx, hxy, hx1, hx2, hy1, hy2⟩
      split_ands; any_goals omega
      rw [Nat.add_sub_assoc, Nat.sq_sub_sq, Nat.sq_sub_sq]
      rw [← hx1, ← hx2, ← hy1, ← hy2]
      repeat rw [Nat.add_sub_cancel_left]
      ring_nf; rw [add_assoc, ← Nat.add_mul, hxy]
      norm_num; apply Nat.pow_le_pow_left; omega
    rintro ⟨blta, cltb, dltc, dpos, h1, h2⟩
    rw [Nat.add_sub_assoc, Nat.sq_sub_sq, Nat.sq_sub_sq] at h2
    have h3 : a - b = 1 := by
      by_contra!; rw [ne_iff_lt_or_gt] at this
      rcases this with h|h; omega
      suffices : 2010 < (a + b) * (a - b) + (c + d) * (c - d); omega
      calc
        _ = (a + b) * 1 + (c + d) * 1 := by rw [← h1]; ring
        _ < (a + b) * (a - b) + (c + d) * 1 := by gcongr; omega
        _ ≤ _ := by gcongr; omega
    norm_num [h3] at h2; have h4 : c - d = 1 := by
      by_contra!; rw [ne_iff_lt_or_gt] at this
      rcases this with h|h; omega
      suffices : 2010 < a + b + (c + d) * (c - d); omega
      calc
        _ = a + b + (c + d) * 1 := by rw [← h1]; ring
        _ < _ := by gcongr
    clear h2; use b; split_ands; any_goals omega
    use d; split_ands; any_goals omega
    apply Nat.pow_le_pow_left; omega
-- Prove that $f$ is injective
  have finj : f.Injective := by
    intro p q hpq; simp [f] at hpq
    ext; exact hpq.left; exact hpq.right
-- Use `card_image_of_injective` to rewrite the goal to finding the cardinality of a finite set
  rw [← fimg, Set.ncard_coe_Finset, card_image_of_injective _ finj]
-- Define the following function $g$ and rewrite the goal to finding the cardinality of $[1,501]$, which is trivial
  simp; let g : ℕ → ℕ × ℕ := fun x => (1004 - x, x)
  have gimg : image g (Icc 1 501) = filter (fun p => p.2 < p.1 ∧
  p.1 + p.2 = 1004) (Icc 1 1004 ×ˢ Icc 1 1004) := by
    simp [Finset.ext_iff, g, and_assoc]; intro b d
    constructor
    · rintro ⟨x, xge, xle, hx1, hx2⟩; split_ands
      all_goals omega
    rintro ⟨dge, dle, bge, ble, dltb, hbd⟩
    use d; split_ands; all_goals omega
  have ginj : g.Injective := by
    intro p q hpq; simp [g] at hpq
    exact hpq.right
  rw [← gimg, card_image_of_injective _ ginj]
  norm_num