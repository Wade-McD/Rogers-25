theory Buff_desc
  imports "HOL-Library.Word"
begin

(*
lemma split_cat_eq:
  fixes x :: \<open>'a::len word\<close> and y :: \<open>'b::len word\<close> and z :: \<open>'c::len word\<close>
  assumes "LENGTH('a) = LENGTH('b) + LENGTH('c)"
  shows \<open>word_split x = (y,z) \\<open>Longrightarrow\<close> word_cat y z = x\<close>
  apply (simp add: word_split_def word_cat_def)
*)

chapter \<open>Abstract specification for UDP wrap\<close>

text \<open>define octets and messages\<close>
type_synonym octet = \<open>8 word\<close>
type_synonym message = \<open>octet list\<close>

text \<open>An IPv6 address consists of eight groups of 16 bits.\<close>
type_synonym ip_addr_d = "16 word \<times> 16 word \<times> 16 word \<times> 16 word \<times> 16 word \<times> 16 word \<times> 16 word \<times> 16 word"


text \<open>we define a memory region indexed by a 64 bit word populated (potentially sparsely) by octets.\<close>
type_synonym memregion_int = \<open>64 word\<close>
type_synonym memregion = "memregion_int \<Rightarrow> octet option"


text \<open>we model a buffer as a list of octets\<close>
type_synonym buf = "octet list"

record net_buf_desc =
  offset :: memregion_int
  len :: \<open>16 word\<close>

definition "buf_size \<equiv> 2048"
definition "bufs_per_region \<equiv> 512"


text \<open>for now, a state consists of one memory region\<close>
record state =
  buf_memregion :: memregion

text \<open>write a buffer into a memory region at a specified location\<close>
definition write_buf :: "memregion_int \<Rightarrow> buf \<Rightarrow> memregion \<Rightarrow> memregion"
  where "write_buf ptr buffer region \<equiv> \<lambda> n.
          if (n \<ge> ptr \<and> (unat n) < ((unat ptr) + length buffer))
          then (Some (buffer ! (unat (n-ptr))))
          else (region n)
        "

value "(write_buf 16 [1,2,3] (\<lambda>n. None)) 2"


text \<open>lift this definition into a state transformation\<close>
definition buf_state_to_written_buf_state :: "64 word \<Rightarrow> buf \<Rightarrow> state => state"
  where "buf_state_to_written_buf_state ptr buffer \<equiv>
        \<lambda>(s::state). (s \<lparr>buf_memregion := write_buf ptr buffer (buf_memregion s)\<rparr>)"


definition write_buf_state :: "64 word \<Rightarrow> buf \<Rightarrow> (state, unit) nondet_monad"
  where \<open>write_buf_state ptr buffer \\<open>equiv\<close> modify (buf_state_to_written_buf_state ptr buffer)\<close>



end