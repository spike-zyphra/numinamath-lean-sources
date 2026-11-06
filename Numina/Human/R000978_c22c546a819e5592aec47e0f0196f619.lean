import Mathlib

/- If $r$ is a positive integer such that $\mathop{\text{lcm}}[r,100]\cdot\gcd(r,100) = 13200$, then what is $\mathop{\text{lcm}}[r,100]$? -/
theorem number_theory_19532 (r : ℕ) (hr : r > 0) (h : Nat.lcm r 100 * Nat.gcd r 100 = 13200) :
    Nat.lcm r 100 = 3300 := by
  -- notice that gcd(a,b) * (lcm a, b) = a*b
  have h1: r.lcm 100 * r.gcd 100 = r*100 := by
    rw [mul_comm]
    apply Nat.gcd_mul_lcm
  -- so we know r = 132
  have hr: r = 132 := by
    have: 13200 = 132*100 := by norm_num
    rw [h1, this] at h
    linarith [h]
  -- to calculate lcm, we can use lcm = (lcm*gcd)/gcd. so we work on gcd first.
  -- 132/4 = 33, 100/4 = 25, 33 and 25 are coprime. so gcd is 4.
  have h2: r.gcd 100 = 4 := by
    rw [hr]
    rw [Nat.gcd_eq_iff]
    constructor; omega; constructor; omega
    intro c cdv1 cdv2
    have h132: 132 = 4 * 33 := by norm_num
    rw [h132] at cdv1
    rw [dvd_mul] at cdv1
    rcases cdv1 with ⟨e1,e2,he⟩
    have he2: e2 = 1 := by
      have e2dv := he.right.left
      have: e2 = 1 ∨ e2 = 3 ∨ e2 = 11 ∨ e2 = 33 := by
        -- e2 divide 33, factors of 33 are only 1,3,11,33.
        have hub: e2 ≤ 33 := by
          apply Nat.le_of_dvd (by norm_num) e2dv
        have: ∀n:ℕ, n ≤ 33 → n ∣ 33 → 
          n=1 ∨ n=3 ∨ n=11 ∨ n=33 := by decide
        apply this e2 hub e2dv
      have e2dv': e2 ∣ 100 := by
        have: e2 ∣ c := by
          use e1; rw [mul_comm]; apply he.right.right
        apply dvd_trans this cdv2      
      rcases this with eq | eq | eq | eq
      <;> rw [eq]
      <;> rw [eq] at e2dv' <;> norm_num at e2dv'
    rw [he2] at he; simp at he
    rw [← he.right] at he
    exact he.left
  -- lcm * 4 =13200, so lcm = 3300
  have h3: 13200 = 3300 * 4 := by norm_num
  rw [h2, h3] at h
  linarith [h]