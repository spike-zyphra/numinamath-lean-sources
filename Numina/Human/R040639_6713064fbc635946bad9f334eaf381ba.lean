import Mathlib

lemma lcm_expend{x y a b m n:Nat}(h1:x+y ≡ a [MOD m])(h2: x+y ≡ b [MOD n])(h3:  lcm m n ∣ y):(x ≡ a [MOD m]) ∧ (x ≡ b [MOD n]):= by
-- prove x+ma % m = x, same as y
  have hs1: m ∣ y:= by apply dvd_trans _ h3;exact Nat.dvd_lcm_left m n
  have hs2: n ∣ y:= by apply dvd_trans _ h3;exact Nat.dvd_lcm_right m n
  -- prove m ∣ y ,n ∣ y
  have hs1:= Dvd.dvd.modEq_zero_nat hs1
  have hs2:= Dvd.dvd.modEq_zero_nat hs2
  -- prove y ≡ 0 [MOD m] ,y ≡ 0 [MOD n]
  constructor
  have h0a:a = 0+a:= by simp
  have h0b:b = 0+b:= by simp
  rw [h0a,add_comm] at h1
  rw [h0b,add_comm] at h2
  -- use a%b+c%b=(a+c)%b
  apply Nat.ModEq.add_left_cancel hs1 h1
  apply Nat.ModEq.add_right_cancel hs2 h2

lemma lcm_expend4{a1 b1 a2 b2 a3 b3 a4 b4 x y: Nat}(h: ((x+y ≡ a1 [MOD b1]) ∧ (x+y ≡ a2 [MOD b2])) ∧((x+y ≡ a3 [MOD b3]) ∧(x+y ≡ a4 [MOD b4])))
    (h3:  ((lcm b1 b2).lcm (lcm b3 b4)) ∣ y):((x ≡ a1 [MOD b1]) ∧ (x ≡ a2 [MOD b2])) ∧((x ≡ a3 [MOD b3]) ∧(x ≡ a4 [MOD b4]))
  := by
  constructor
  -- use lcm_expend to prove
  apply lcm_expend h.1.1 h.1.2
    -- reuse condition
  apply dvd_trans _ h3;exact Nat.dvd_lcm_left _ _
  apply lcm_expend h.2.1 h.2.2
  -- reuse condition
  apply dvd_trans _ h3;exact Nat.dvd_lcm_right _ _

def solve_4709(a1 b1 a2 b2 a3 b3 a4 b4 z: Nat)(h:z=(lcm (lcm b1 b2) (lcm b3 b4))):Finset (Fin z):=
  {x:(Fin z)| ((x ≡ a1 [MOD b1]) ∧ (x ≡ a2 [MOD b2])) ∧((x ≡ a3 [MOD b3]) ∧(x ≡ a4 [MOD b4]))} --find the base solutions

lemma t3:30 =(lcm (lcm 6 10) (lcm 15 15)):= by native_decide

/- 8. Using the method from problem 7, solve the following simultaneous system of congruences:
a) \( x \equiv 4 \pmod{6} \)
b) \( x \equiv 7 \pmod{10} \)
c) \( x \equiv 13 \pmod{15} \)
d) \( x \equiv 4 \pmod{15} \)-/
theorem number_theory_4709 (x : Nat) (h : ((x ≡ 4 [MOD 6]) ∧ (x ≡ 7 [MOD 10])) ∧((x ≡ 13 [MOD 15]) ∧(x ≡ 4 [MOD 15])))
    :False:= by
  have hc: 1 < 30 := by norm_num
  have hs: (solve_4709 4 6 7 10 13 15 4 15 30 t3) = ∅:= by native_decide
  -- show the base solution
  by_cases hx: x<30
  --consider hx:x<30
  let z: Fin 30 := ⟨x,hx⟩
  have hz: z ∈ (solve_4709 4 6 7 10 13 15 4 15 30 t3):= by
    simp [solve_4709]
    exact h
  -- find the solution
  rw [hs] at hz
  --find a contraditon
  trivial

  have hcons:=Nat.mod_add_div x 30
  let z: Fin 30 := ⟨x%30,by apply Nat.mod_lt;norm_num⟩
  -- condiser fin cases
  rw [← hcons] at h
  have hrr:= lcm_expend4 h (by apply Nat.dvd_mul_right)
  -- use
  have hzz: z ∈ solve_4709 4 6 7 10 13 15 4 15 30 t3 := by
      simp [solve_4709]
      exact hrr
  rw [hs] at hzz
  trivial
