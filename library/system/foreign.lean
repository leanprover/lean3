namespace foreign

open nat

def bounded (a p q : ℤ) := p ≤ a ∧ a < q

structure irange (l u : ℤ) :=
(val : ℤ)
(bounded : bounded val l u)

namespace irange

protected def lt {p q} (a b : irange p q) : Prop :=
a.val < b.val

protected def le {p q} (a b : irange p q) : Prop :=
a.val ≤ b.val

instance {p q} : has_lt (irange p q)  := ⟨irange.lt⟩
instance {p q} : has_le (irange p q)  := ⟨irange.le⟩

instance decidable_lt {p q} (a b : irange p q) :  decidable (a < b) :=
int.decidable_lt _ _

instance decidable_le {p q} (a b : irange p q) : decidable (a ≤ b) :=
int.decidable_le _ _

def {u} elim0 {α : Sort u} {p} : irange p p → α
| ⟨_, h₀, h₁⟩ := false.elim (not_lt_of_ge h₀ h₁)

variable {n : nat}

lemma eq_of_veq {p q} : ∀ {i j : irange p q}, (val i) = (val j) → i = j
| ⟨iv, ilt₁, glt₁⟩ ⟨.(iv), ilt₂, glt₂⟩ rfl := rfl

lemma veq_of_eq {p q} : ∀ {i j : irange p q}, i = j → (val i) = (val j)
| ⟨iv, ilt, igt⟩ .(_) rfl := rfl

lemma ne_of_vne {p q} {i j : irange p q} (h : val i ≠ val j) : i ≠ j :=
λ h', absurd (veq_of_eq h') h

lemma vne_of_ne {p q} {i j : irange p q} (h : i ≠ j) : val i ≠ val j :=
λ h', absurd (eq_of_veq h') h

end irange

open irange

instance (p q : ℤ) : decidable_eq (irange p q) :=
λ i j, decidable_of_decidable_of_iff
  (int.decidable_eq i.val j.val) ⟨eq_of_veq, veq_of_eq⟩

namespace irange
open int
variables {p q : int}

protected def succ : irange p q → irange p (q+1)
| ⟨a, h, h'⟩ := ⟨a+1, le_trans h (le_add_of_nonneg_right zero_le_one), add_lt_add_right h' _⟩

section truncate

def truncate (x p q : ℤ) := (x - p) % (q - p) + p

variables {x : ℤ} {p q}
variables (y : ℤ) (h : p ≤ y) (h' : y < q)

private lemma pos_q_sub_p : 0 < (q - p) :=
sub_pos_of_lt (lt_of_le_of_lt h h')

private lemma q_sub_p_ne_zero :  (q - p) ≠ 0 :=
ne_of_gt (pos_q_sub_p _ h h')

lemma le_truncate : p ≤ truncate x p q :=
le_add_of_sub_right_le $
suffices 0 ≤ (x - p) % (q - p), by simp * at *,
int.nonneg_mod (q_sub_p_ne_zero _ h h')

lemma truncate_lt : truncate x p q < q :=
add_lt_of_lt_sub_right $ int.mod_lt $ pos_q_sub_p y h h'

lemma bounded_truncate (h : foreign.bounded y p q) : foreign.bounded (truncate x p q) p q :=
⟨ le_truncate _ h.1 h.2, truncate_lt _ h.1 h.2 ⟩

lemma bounded_zero {p q : ℕ} : foreign.bounded 0 (-p) q.succ :=
⟨ neg_le_of_neg_le (coe_nat_le_coe_nat_of_le $ nat.zero_le _), coe_nat_lt_coe_nat_of_lt (nat.zero_lt_succ _) ⟩

end truncate

def of_int {p q : ℕ} (a : int) : irange (- p) q.succ :=
⟨ truncate a (-p) (succ q), bounded_truncate 0 bounded_zero ⟩

protected def add : irange p q → irange p q → irange p q
| ⟨a, h⟩ ⟨b, _⟩ := ⟨truncate (a + b) p q, bounded_truncate _ h⟩

protected def mul : irange p q → irange p q → irange p q
| ⟨a, h⟩ ⟨b, _⟩ := ⟨truncate (a * b) p q, bounded_truncate _ h⟩

protected def sub : irange p q → irange p q → irange p q
| ⟨a, h⟩ ⟨b, _⟩ := ⟨truncate (a - b) p q, bounded_truncate _ h⟩

protected def mod : irange p q → irange p q → irange p q
| ⟨a, h⟩ ⟨b, _⟩ := ⟨truncate (a % b) p q, bounded_truncate _ h⟩

protected def div : irange p q → irange p q → irange p q
| ⟨a, h⟩ ⟨b, _⟩ := ⟨truncate (a / b) p q, bounded_truncate _ h⟩

instance {p q : ℕ} : has_zero (irange (-p) q.succ) := ⟨of_int 0⟩
instance {p q : ℕ} : has_one (irange (-p) q.succ) := ⟨of_int 1⟩
instance : has_add (irange p q)         := ⟨irange.add⟩
instance : has_sub (irange p q)         := ⟨irange.sub⟩
instance : has_mul (irange p q)         := ⟨irange.mul⟩
instance : has_mod (irange p q)         := ⟨irange.mod⟩
instance : has_div (irange p q)         := ⟨irange.div⟩
instance : has_repr (irange p q)        := ⟨repr ∘ irange.val⟩

lemma of_int_zero {p q : ℕ} : @of_int p q 0 = 0 := rfl

lemma add_def (a b : irange p q) : (a + b).val = truncate (a.val + b.val) p q :=
show (irange.add a b).val = truncate (a.val + b.val) p q, from
by cases a; cases b; simp [irange.add]

lemma mul_def (a b : irange p q) : (a * b).val = truncate (a.val * b.val) p q :=
show (irange.mul a b).val = truncate (a.val * b.val) p q, from
by cases a; cases b; simp [irange.mul]

lemma sub_def (a b : irange p q) : (a - b).val = truncate (a.val - b.val) p q :=
show (irange.sub a b).val = truncate (a.val - b.val) p q, from
by cases a; cases b; simp [irange.sub]

lemma mod_def (a b : irange p q) : (a % b).val = truncate (a.val % b.val) p q :=
show (irange.mod a b).val = truncate (a.val % b.val) p q, from
by cases a; cases b; simp [irange.mod]

lemma div_def (a b : irange p q) : (a / b).val = truncate (a.val / b.val) p q :=
show (irange.div a b).val = truncate (a.val / b.val) p q, from
by cases a; cases b; simp [irange.div]

lemma lt_def (a b : irange p q) : (a < b) = (a.val < b.val) :=
show (irange.lt a b) = (a.val < b.val), from
by cases a; cases b; simp [irange.lt]

lemma le_def (a b : irange p q) : (a ≤ b) = (a.val ≤ b.val) :=
show (irange.le a b) = (a.val ≤ b.val), from
by cases a; cases b; simp [irange.le]

lemma val_zero {p q : ℕ} : (0 : irange (-p) q.succ).val = 0 :=
show truncate 0 _ _ = 0, from
sub_eq_zero_of_eq $
begin
  suffices : p % (q.succ + p) = p,
  { conv { to_rhs, rw ← this }, simp, refl },
  apply mod_eq_of_lt, apply lt_add_of_zero_lt_right,
  apply zero_lt_succ,
end

end irange

@[reducible]
def uint_8 := fin $ succ 255
@[reducible]
def uint_16 := fin $ succ 65535
@[reducible]
def uint_32 := unsigned
@[reducible]
def uint_64 := fin $ succ 18446744073709551615

@[reducible]
def int_8 := irange (-succ 127) (succ 127)
@[reducible]
def int_16 := irange (-succ 32767) (succ 32767)
@[reducible]
def int_32 := irange (-succ 2147483647) (succ 2147483647)
@[reducible]
def int_64 := irange (-succ 9223372036854775807) (succ 9223372036854775807)

end foreign
