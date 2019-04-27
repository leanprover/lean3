import system.io

open io io.fs

def TEST_DIR : string := "_test_dir"
def TEST_DIR1 : string := "_test_dir1"
def TEST_DIR2 : string := "_test_dir2"
def TEST_FILE_1 : string := "_test_file1"
def TEST_FILE_2 : string := "_test_file2"

meta def ycheck (s : string) (t : io bool) : io unit :=
do r ← t,
   if r then return ()
        else io.fail sformat!"ycheck: {s}"

meta def ncheck (s : string) (t : io bool) : io unit :=
do r ← t,
   if ¬r then return ()
         else io.fail sformat!"ncheck: {s}"

meta def go_dir : io unit :=
do rmdir TEST_DIR,
   ncheck "dir exists now" $ dir_exists TEST_DIR,
   ycheck "mkdir" $ mkdir TEST_DIR,
   ycheck "dir exists now" $ dir_exists TEST_DIR,
   ncheck "file exists now" $ file_exists TEST_DIR,
   ycheck "rmdir" $ rmdir TEST_DIR,
   ncheck "dir exists now'" $ dir_exists TEST_DIR,
   return ()

meta def go_dir_recursive : io unit :=
do let combined := TEST_DIR1 ++ "/" ++ TEST_DIR2,
   rmdir $ combined,
   rmdir TEST_DIR1,
   ycheck "mkdir rec" $ mkdir combined tt,
   ycheck "dir exists now1" $ dir_exists TEST_DIR1,
   ycheck "dir exists now2" $ dir_exists combined,
   ycheck "rmdir2" $ rmdir $ combined,
   ycheck "dir exists now1'" $ dir_exists TEST_DIR1,
   ncheck "dir exists now2'" $ dir_exists combined,
   ycheck "rmdir" $ rmdir $ TEST_DIR1,
   ncheck "dir exists now1''" $ dir_exists TEST_DIR1,
   ncheck "dir exists now2''" $ dir_exists combined,
   return ()

meta def go_file : io unit :=
do remove TEST_FILE_1 <|> return (),
   remove TEST_FILE_2 <|> return (),
   ncheck "file1 exists now" $ file_exists TEST_FILE_1,
   mk_file_handle TEST_FILE_1 io.mode.write >>= close,
   ycheck "file1 exists now'" $ file_exists TEST_FILE_1,
   ncheck "dir exists now" $ dir_exists TEST_FILE_1,
   rename TEST_FILE_1 TEST_FILE_2,
   ncheck "file1 exists now''" $ file_exists TEST_FILE_1,
   ycheck "file2 exists now" $ file_exists TEST_FILE_2,
   remove TEST_FILE_2,
   ncheck "file2 exists now" $ file_exists TEST_FILE_2,
   return ()

run_cmd (tactic.unsafe_run_io go_dir)
run_cmd (tactic.unsafe_run_io go_dir_recursive)

run_cmd (tactic.unsafe_run_io go_file)