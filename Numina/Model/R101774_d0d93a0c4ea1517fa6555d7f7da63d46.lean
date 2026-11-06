import Mathlib

def S : Finset ℕ := Finset.Icc 1 10000

def A : Finset ℕ := S.filter (fun n => 2 ∣ n)
def B : Finset ℕ := S.filter (fun n => 3 ∣ n)
def C : Finset ℕ := S.filter (fun n => 5 ∣ n)
def D : Finset ℕ := S.filter (fun n => 7 ∣ n)

theorem number_theory_7895 :
    {n | n ∈ S ∧ ¬(2 ∣ n) ∧ ¬(3 ∣ n) ∧ ¬(5 ∣ n) ∧ ¬(7 ∣ n)}.ncard = 2285 := by 
  have h1 : {n | n ∈ S ∧ ¬(2 ∣ n) ∧ ¬(3 ∣ n) ∧ ¬(5 ∣ n) ∧ ¬(7 ∣ n)} = Finset.filter (fun n => ¬(2 ∣ n) ∧ ¬(3 ∣ n) ∧ ¬(5 ∣ n) ∧ ¬(7 ∣ n)) S := by
    ext n
    simp [S]
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide