From refinedrust Require Import typing.
From stdlib.ptr.ptr.generated Require Import generated_specs_ptr.

Record rust_layout := mk_rust_layout {
  layout_sz : Z;
  layout_alignment : alignment_enum;
}.
Global Instance rust_layout_inh : Inhabited rust_layout.
Proof. exact (populate (mk_rust_layout inhabitant inhabitant)). Qed.
