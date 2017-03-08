import init.data.quot
universe u

def defined_array.equiv (α) {n} (s : set (fin n)) (a b : array α n) := ∀ x ∈ s, a^.read x = b^.read x

def defined_array.setoid (α) {n} (s : set (fin n)) : setoid (array α n) :=
⟨defined_array.equiv α s,
 λa x _, rfl,
 λa b ab x h, eq.symm (ab x h),
 λa b c ab bc x h, eq.trans (ab x h) (bc x h)⟩

def defined_array (α) {n} (s : set (fin n)) := quotient (defined_array.setoid α s)

def defined_array.lift_on {α n s} (q : @defined_array α n s) (β) (f : array α n → β)
  (h : ∀ (a b : array α n), (∀ x ∈ s, a^.read x = b^.read x) → f a = f b) : β :=
@quotient.lift _ β (defined_array.setoid α s) f h q

def defined_array.read {α n s} (q : @defined_array α n s) (x) (h : x ∈ s) : α :=
q^.lift_on (Π x ∈ s, α) (λa x _, a^.read x) (λ a b ab, funext $ λ x, funext $ λh, ab x h) x h

def defined_array.write {α n s} (q : @defined_array α n s) (x) (h : x ∈ s) (v : α) : defined_array α s :=
q^.lift_on _ (λa, @quotient.mk _ (defined_array.setoid α s) $ a^.write x v)
  (λa b h, quot.sound (λi hi, show (if x = i then v else a^.read i) = (if x = i then v else b^.read i), by rw h i hi))

def array_list.valid (size capacity) : set (fin capacity) := λ ⟨x, h⟩, x < size

structure array_list (α : Type u) :=
(capacity length : nat)
(data : defined_array α (array_list.valid length capacity))
(len_le : length ≤ capacity)

def array_list.mk_data {α length capacity} (a : array α capacity) : defined_array α (array_list.valid length capacity) :=
@quotient.mk _ (defined_array.setoid α (array_list.valid length capacity)) a

local notation `⟦`:max a `⟧` := array_list.mk_data a

def mk_array_list {α} [inhabited α] (capacity := 10) : array_list α :=
{ capacity := capacity,
  length := 0,
  data := ⟦mk_array capacity (default α)⟧,
  len_le := nat.zero_le capacity }

def array.to_array_list {α n} (l : array α n) : array_list α :=
{ capacity := n,
  length := n,
  data := ⟦l⟧,
  len_le := le_refl n }

def mk_array_list_of_fn {α n cap} [inhabited α] (f : fin n → α) (H : n ≤ cap) : array_list α :=
{ capacity := cap,
  length := n,
  data := ⟦{data := λ⟨x, _⟩, if h : x < n then f ⟨x, h⟩ else default α}⟧,
  len_le := H }

def array.to_array_list_cap {α n cap} [inhabited α] (arr : array α n) (H : n ≤ cap) : array_list α :=
mk_array_list_of_fn arr^.read H

namespace array_list

def nil {α} : array_list α :=
{ capacity := 0,
  length := 0,
  data := ⟦array.nil⟧,
  len_le := le_refl 0 }

lemma lt_capacity {α} (l : array_list α) {n} (h : n < l^.length) : n < l^.capacity :=
nat.lt_of_lt_of_le h l^.len_le

def read {α} (l : array_list α) (x : fin l^.length) : α :=
let ⟨n, h⟩ := x in l^.data^.read ⟨n, l^.lt_capacity h⟩ h

def to_array {α} (l : array_list α) : array α l^.length :=
{data := l^.read}

def write {α} (l : array_list α) : fin l^.length → α → array_list α :=
λ ⟨n, h⟩ v, { l with data := l^.data^.write ⟨n, l^.lt_capacity h⟩ h v }

def trim {α} (l : array_list α) : array_list α :=
l^.to_array^.to_array_list

def truncate {α} (l : array_list α) (n) (nsz : n ≤ l^.length) : array_list α :=
{ capacity := l^.capacity,
  length := n,
  data := l^.data^.lift_on _ (λa, ⟦a⟧) (λa b H, quot.sound (λ⟨x, h⟩ (hn : x < n), H ⟨x, h⟩ (lt_of_lt_of_le hn nsz))),
  len_le := le_trans nsz l^.len_le }

def ensure_capacity {α} [inhabited α] (l : array_list α) (cap : nat) : array_list α :=
if H : l^.capacity ≥ cap then l else
@mk_array_list_of_fn α l^.length (max cap (2 * l^.length)) _ l^.read $
  le_trans l^.len_le $ le_trans (le_of_lt $ lt_of_not_ge H) (le_max_left _ _)

theorem ensure_capacity_len {α} [inhabited α] (l : array_list α) (cap : nat) : (ensure_capacity l cap)^.length = l^.length :=
if H : l^.capacity ≥ cap
then begin delta ensure_capacity, rwa dif_pos H end
else begin delta ensure_capacity, rw dif_neg H, reflexivity end

theorem ensure_capacity_ge {α} [inhabited α] (l : array_list α) (cap : nat) : (ensure_capacity l cap)^.capacity ≥ cap :=
if H : l^.capacity ≥ cap
then begin delta ensure_capacity, rwa dif_pos H end
else begin delta ensure_capacity, rw dif_neg H, exact le_max_left _ _ end

def append {α} (l : array_list α) (v : α) : array_list α :=
let L := @ensure_capacity _ ⟨v⟩ l (l^.length + 1) in
have llen : L^.length = l^.length, from @ensure_capacity_len _ ⟨v⟩ l (l^.length + 1),
have lc : l^.length < L^.capacity, from @array_list.ensure_capacity_ge _ ⟨v⟩ l (l^.length + 1),
{ capacity := L^.capacity,
  length := l^.length + 1,
  data := L^.data^.lift_on _
    (λa, ⟦a^.write ⟨l^.length, lc⟩ v⟧)
    (λa b H, quot.sound $ λ ⟨y, yl⟩ hi,
      let lf := fin.mk l^.length lc in
      show (if lf = ⟨y, yl⟩ then v else a^.read ⟨y, yl⟩) = (if lf = ⟨y, yl⟩ then v else b^.read ⟨y, yl⟩), from
      if h : lf = ⟨y, yl⟩ then by repeat {rw if_pos h} else
      have y < L^.length, from eq.symm llen ▸ lt_of_le_of_ne (nat.le_of_succ_le_succ hi)
        (λe : (fin.mk y yl)^.val = (fin.mk l^.length lc)^.val, h $ fin.eq_of_veq $ eq.symm e),
      by repeat {rw if_neg h}; exact H ⟨y, yl⟩ this),
  len_le := lc }

def append_list {α} [inhabited α] : array_list α → list α → array_list α
| l [] := l
| l (x :: xs) := append_list (l^.append x) xs

-- make sure this is compiled with overwrite optimization
def insert_aux {α} : Π n (l : array_list α) (h : n ≤ l^.length), α → array_list α
| 0 l h v := append l v
| (n+1) l h v :=
  let pos := fin.mk (l^.length - 1 - n) (array.lt_aux_3 h) in
  let u := l^.read pos in insert_aux n (l^.write pos v) (le_of_lt h) u

def insert {α} (l : array_list α) (v : α) (n : ℕ) (h : n ≤ l^.length) : array_list α :=
insert_aux (l^.length - n) l (nat.sub_le _ _) v

-- TODO (Mario): add operations for adding and removing several elements at a time
def remove_aux {α} : Π n (l : array_list α) (h : n < l^.length), array_list α
| 0 l h := l^.truncate (l^.length - 1) $ nat.sub_le _ _
| (n+1) l h :=
  let pos := l^.length - 1 - n in
  let u := l^.read ⟨pos, array.lt_aux_3 $ le_of_lt h⟩ in
  remove_aux n (l^.write ⟨pos - 1, by rw nat.sub_sub; exact array.lt_aux_3 h⟩ u) (le_of_lt h)

def remove {α} (l : array_list α) (n : ℕ) (h : n < l^.length) : array_list α :=
remove_aux (l^.length - 1 - n) l (array.lt_aux_3 h)

def clear {α} (l : array_list α) : array_list α :=
l^.truncate 0 (nat.zero_le _)

def to_list_aux {α} (l : array_list α) : Π n ≤ l^.length, list α
| 0     h := []
| (n+1) h := l^.read ⟨l^.length - 1 - n, begin
    rw nat.sub_sub,
    apply nat.sub_lt,
    apply lt_of_lt_of_le (nat.zero_lt_succ _) h,
    rw add_comm,
    apply nat.zero_lt_succ
  end⟩ :: to_list_aux n (nat.le_of_succ_le h)

def to_list {α} (l : array_list α) : list α :=
to_list_aux l l^.length (le_refl _)

end array_list

def list.to_array_list {α} (l : list α) : array_list α :=
l^.to_array^.to_array_list