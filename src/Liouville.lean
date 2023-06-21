/-
In this file we will prove Liouville's Theorem in the usual form for irrational α in ℝ.
We will follow Zannier's "Lecture Notes on Diophantine Analysis" where the Liouville's Theorem is Theorem 2.3
-/
import field_theory.minpoly.is_integrally_closed
import data.real.irrational
import analysis.calculus.cont_diff
import data.polynomial.denoms_clearable
import algebra.gcd_monoid.finset
import data.rat.defs
open_locale classical big_operators polynomial
open polynomial


--import data.polynomial
-- import analysis.calculus.mean_value
--MEAN VALUE THEOREM is
-- exists_has_deriv_at_eq_slope
-- LIOUVILLE IN MATHLIB
-- import number_theory.liouville.basic

-- import topology.algebra.ordered
-- EXTREME VALUE THEOREM (continuous function on compact obtains max)
-- is_compact.exists_forall_ge

noncomputable theory

-- notation `transcendental` x := ¬(is_algebraic ℤ x)


/- 
Servirebbe lemma che passa dal minpoly al polinomio in ℤ[X] primitivo di grado minimo che si annulla in x, per poter richimare il lemma qui sotto
 

Messaggio di Filippo:
 Io farei così: prima definisci una funzione
lean
def pippo : polynomial rat -> polynomial int :=

che prende un polinomio razionale e lo moltiplica per i coefficienti; mentre lo costruisci, ti scontri con la definizione di polinomio che è in docs#polynomial e che ti richiede per ogni `n : nat` un elemento di `int`; tu gli dai il coefficiente del polinomio razionale moltiplicato per il mcm, e poi applichi 
docs#rat.denom_eq_one_iff.

serve:


rat.denom_eq_one_iff


per lcm: guardare polynomial.integral_normalization

 -/

#eval (rat.mk 4 2)

 lemma aux (n :ℕ  ) (hn: n≠ 0)  (x :ℚ )  : (↑ n * x ).denom=1 ↔  ↑x.denom ∣ n :=
 begin
  rw [rat.mul_num_denom , rat.coe_nat_denom , rat.coe_nat_num],
  simp,
  have  hd:  (gcd n x.denom : ℤ)  ≠ 0, {
    rw <- int.cast_zero,
    by_contra,
    rw gcd_eq_zero_iff at h,
    norm_cast at h,
    exact hn h.1,
    sorry,
  },
  have hnd: gcd n x.denom ∣ n, exact gcd_dvd_left _ _,
  have hden: gcd n x.denom ∣ x.denom, exact gcd_dvd_right _ _,
  cases hnd with wn hwn,
  cases hden with wd hwd,
  nth_rewrite 0 [hwn],
  nth_rewrite 1 [hwd],
  nth_rewrite 0 mul_comm,
  nth_rewrite 1 mul_comm,
  nth_rewrite 2 mul_comm,
  push_cast,
  rw <-mul_assoc,
  rw rat.div_mk_div_cancel_left, 
  swap, exact hd,

  simp,
  split, {
    --rw [rat.coe_int_eq_mk, rat.mul_def (one_ne_zero) hb],
    intro h,

  }
 end

def denom_coeffs (p : ℚ[X]): ℕ → ℕ := λ n,  (p.coeff n).denom

def lcm_denom_coeffs (p : ℚ[X]) : ℕ  := (p.support).lcm (denom_coeffs p)

#check {0,1,2}

#eval {0,1,2}.lcm ((monomial 2 3 + monomial 1 6 + monomial 0 1).coeff)


theorem canc_denom_int (p : ℚ[X]) : ∀ n: ℕ , ↑(↑(lcm_denom_coeffs p) * (p.coeff n)).num=(↑(lcm_denom_coeffs p) * (p.coeff n)):=
begin
  intro n,
  rw <-rat.denom_eq_one_iff,
 -- rw rat.mul_def,
  sorry,
end


def canc_denom2  (p : ℚ[X]) : ℚ[X] := (lcm_denom_coeffs p) • p 

def canc_denom (p : ℚ[X]) : ℚ[X] := 
∑ i in p.support,  monomial i  (↑(lcm_denom_coeffs p) * (p.coeff i))


def canc_denom3 : ℚ[X]→ ℤ [X]:= λ p,  ∑ i in p.support,  monomial i  (↑(lcm_denom_coeffs p) * (p.coeff i)).num



theorem same_roots : ∀ p:ℚ[X], ∀ x:ℝ, polynomial.eval₂ (algebra_map ℚ ℝ) (x) p =0 ↔  polynomial.eval₂ (algebra_map ℤ  ℝ) (x) (canc_denom3 p)=0:=
begin
  intros p x,
  --rw canc_denom3,
  split,{
    intro h,
    --simp,
    rw [polynomial.eval₂_eq_sum , polynomial.sum_def],
    simp,
    rw canc_denom3,
    sorry,
  },
end

-- def to_subring
/- 
def pol: ℚ [X]:= 
X^2+ (1/2)* X +1/3

example : lcm_denom_coeffs pol = 6 :=
begin
  unfold lcm_denom_coeffs,
  have h1 : (pol).support= { 0,1,2},{
    rw finset.ext_iff,
    intro a,
    split,{
      --rw pol,
      intro ha,
      by_cases a<3,{
        sorry,
      },
      rw not_lt at h,
      exfalso,
      rw pol at ha,
      sorry,
    },
    --rw finsupp.mem_support_iff,
    sorry,
  },
  rw h1,
  rw pol,
  sorry,
end

 -/
/- 

Scusate per il casino, ho fatto esperimenti che non vorrei cancellare


def pol: ℚ [X]:=
X^2+ (1/2)* X +1/3

open set

example : lcm_denom_coeffs pol = 6 :=
begin
  unfold lcm_denom_coeffs,
  have h1 : (pol).support= { 0,1,2},{
    rw finset.ext_iff,
    intro a,
    split,{
      --rw pol,
      intro ha,
      by_cases a<3,{
        sorry,
      },
      rw not_lt at h,
      exfalso,
      rw pol at ha,
      sorry,
    },
    --rw finsupp.mem_support_iff,
    sorry,
  },
  rw h1,
  rw pol,
  sorry,
end

#eval gcd (6:ℤ)  (-9:ℤ )

example : (gcd (6:ℤ ) (9:ℤ ) )  = ↑ 3 :=
begin
  have h1 : 3 ∣ 6, use 2, ring,
  have h2 : 3 ∣ 9, use 3, ring,
  have h3 : ∀ c:ℤ  , c∣ 6→ c∣ 9→c∣ 3,{
    intros c hc1 hc2,
    cases hc1 with a ha,
    cases hc2 with b hb,
    use b-a,
    calc 3=9-6 : by ring
      ... = c * b-6 : by rw hb
      ... = c*b- c* a : by rw ha
      ... = c*(b-a) : by linarith,
  },
  apply associa
  --dvd_gcd_iff
end


 -/



 

/-
 The Lemma gives a lower bound on the absolute value of a polynomial f with integral coefficients evaluated at a rational number x which is not a root of f 
 -/
lemma poly_not_zero_low_bound (a b : ℤ  ) (p : ℤ [X]) (hb : 0<b ) 
(hpab : polynomial.aeval (  (a: ℚ ) / (b  : ℚ  ) ) (polynomial.map (algebra_map ℤ ℚ ) p )≠ 0) :1 ≤ (↑b)^(p.nat_degree)* abs( polynomial.aeval (  (a: ℚ ) / (b  : ℚ  ) ) (polynomial.map (algebra_map ℤ ℚ ) p ))  :=
begin
  exact one_le_pow_mul_abs_eval_div hb hpab,
end

/-
lemma: minimal polynomial of an irrational does not have rational roots
-/
lemma rat_not_root_minpoly_irrat (y : ℚ) (x : ℝ) (hirr : irrational x) (hint: is_integral ℚ x): ¬ (polynomial.is_root (minpoly ℚ x) y):=
begin
  by_contradiction,
  -- minimal polynomial is prime
  have h_prime := minpoly.prime hint,
  -- irreducible polynomial with a root has degree 1
  have h_irr_one := polynomial.degree_eq_one_of_irreducible_of_root (h_prime.irreducible) h,
  -- x is a root of its minimal polynomial
  have h_x_root :=  minpoly.aeval ℚ x,
  -- if x is a root of a degree one polynomial with ℚ coefficients then x ∈ ℚ 
  have h_x_Q := minpoly.mem_range_of_degree_eq_one ℚ x h_irr_one,
  -- Lean is able to figure out the contraddicition using hirr
  tauto,
end

def const_Liouville {x : ℝ} (hint : is_integral ℚ x) : ℝ := 
  sorry

variables {x : ℝ} (hint: is_integral ℚ x) 

lemma const_Liouville_pos : const_Liouville (hint) > 0 :=
  sorry

-- Liouville Theorem
include hint
-- add the hint in the hypothesis using the fact that is included in ``variables'' above
theorem liouville (hirr : irrational x) :   ∀ a b : ℤ, b > 0 → abs(x - (a / b)) > (1 / b^(minpoly ℚ x).nat_degree) :=
begin
-- exact zero_lt_one
intros a b hb,
-- mai UNFOLD definition
-- usare aeval di solito invece che eval₂
-- p is minpoly 
unfold is_integral at hint,
rcases hint with ⟨p, hpmonic, hpzero⟩,
-- richimare lemma che "trasforma" p a coeff in ℤ di grado minimo
-- richimare lemma che "trasforma" p a coeff in ℤ di grado minimo
-- cases hp with hpmonic hpzero,
have h1 : abs((polynomial.eval₂ (algebra_map ℚ ℝ) x p) - (polynomial.eval₂ (algebra_map ℚ ℝ) (↑ a / ↑ b) p)) = abs(polynomial.eval₂ (algebra_map ℚ ℝ) (↑ a / ↑ b) p),
-- the absolute values are the same since x is a zero of its minimal polynomial
{
    -- have := minpoly.aeval ℚ x,
    rw hpzero,
    simp,
},

have hmeanval : ∃ α : ℝ,  (α < x ) ∧ ( α > (↑a / ↑b ) ) ∧ abs((polynomial.eval₂ (algebra_map ℚ ℝ) x p) - (polynomial.eval₂ (algebra_map ℚ ℝ) (↑ a / ↑ b) p)) = abs (x - (↑ a / ↑ b )) * abs (polynomial.eval₂ (algebra_map ℚ ℝ) α (polynomial.derivative p)),
{
  sorry,
},

sorry,
end

