theory Ring

imports "HOL-Library.Word" "Main" "HOL-Library.IArray"

begin


value "plz :: 'a iarray"


record 'a ring_queue =
  data     :: "'a option list" (*The actual list/storage that holds values. 
          It stores elements as option types to distinguish between Some x and None. *)
  capacity :: nat (* The max amount of elements to queue can hold *)
  tail     :: nat (* Index of the element to be enqueued *)
  head     :: nat (* Index of the element to be dequeued *)
  size     :: nat (* Number of elements within the queue *)


definition mk_ring_queue :: "nat \<Rightarrow> 'a ring_queue" where
  "mk_ring_queue cap \<equiv> \<lparr> 
  data = replicate cap None,
  capacity = cap,
  tail = 0,
  head = 0,
  size = 0
\<rparr>"

value "mk_ring_queue 10 :: nat ring_queue"

definition myrq :: "nat ring_queue" where
  "myrq \<equiv> mk_ring_queue 4"


text \<open>Enqueue where is the ring is full and you try to add another element, the ring gets set to None\<close>
fun enqueue_opt :: "'a \<Rightarrow> 'a ring_queue \<Rightarrow> 'a ring_queue option" where
  "enqueue_opt x que = (
     if size que = capacity que then None else 
     let 
      d = data que;
      t = tail que;
      d' = d[t := Some x];
      t' = t + 1 mod capacity que;
      size' = size que + 1
     in Some (que \<lparr> data := d', tail := t', size := size'\<rparr>))"

lemma "size que = capacity que \<Longrightarrow> enqueue x que = None"
  sorry

text \<open>Value demonstartion of how the enqueue_opt works using bind to make sure the types are correct\<close>
value "Option.bind (Option.bind (Some myrq) (enqueue_opt 10))(enqueue_opt 20)"
value "
      Option.bind (
        Option.bind (
           Option.bind (
             Option.bind (
               Option.bind (Some myrq)
               (enqueue_opt 10))
             (enqueue_opt 20))
           (enqueue_opt 30))
         (enqueue_opt 3))
      (enqueue_opt 1)
"

text \<open>enqueue, where if you try to add more items than the queue can hold, return the queue as-is\<close>
definition enqueue :: "'a option \<Rightarrow> 'a ring_queue \<Rightarrow> 'a ring_queue" where
  "enqueue a aq \<equiv> (if size aq < (capacity aq -1) then \<lparr>data = (data aq)[(tail aq) := a],
                   capacity = capacity aq,
                   tail = (tail aq + 1) mod capacity aq,
                   head = head aq,
                   size = size aq + 1\<rparr> else aq)"

text\<open> Dequeue where if you try to remove an item from a ring that has no items the ring gets set to none.
       - When pulling of the element at the head you had 2 cases to consider, if its None or Some\<close>
fun dequeue_opt :: "'a ring_queue \<Rightarrow> ('a \<times> 'a ring_queue) option" where
  "dequeue_opt que = (
     if size que = 0 then None else
       let
         d = data que;
         h = head que;
         Nx = d ! h
       in case Nx of
            None     \<Rightarrow> None 
            | Some x \<Rightarrow>
                let
                  d' = d[h := None];
                  h' = (h + 1) mod capacity que;
                  s' = size que - 1
                in Some (x, que \<lparr> data := d', head := h', size := s' \<rparr>))"



(*
text \<open>dequeue that when you try to pull of an element from  \<close>
fun dequeue :: "'a ring_queue \<Rightarrow> ('a option \<times> 'a ring_queue)" where
  "dequeue que = (
    if size que = 0 then (None, que) else ..
)"
*)
 









end 