import glob2, subprocess

# Finds all litmus tests and run them with herd
# then generates nicely formated result file(s)
HOME        = "/home/user1/"
HERD_DIR    = HOME + "herd/"
HERD        = HERD_DIR + "_build/default/herd/herd.exe"
HERD_LIB    = HERD_DIR + "herd/libdir/"
JAM19       = HOME + "litmus/java/jam19.cat"
JAM21       = HOME + "litmus/java/jam21.cat"
LITMUS_DIR  = HOME + "litmus/java/litmus/"
OUTPUT      = HOME + "results.md"
TIMEOUT     = 60

def get_result(model, test):
    obs = ''
    try:
        result = subprocess.run([HERD, '-I', HERD_LIB, '-model', model, test], 
            stdout=subprocess.PIPE, timeout=TIMEOUT)
        lines = str(result.stdout.decode('utf-8')).splitlines()
        for line in lines:
            if line.startswith("Observation"):
                obs = line.split(' ')[2]
                
    except subprocess.TimeoutExpired as e:
        obs = "timeout"
    
    return obs

all_litmus_tests = glob2.glob(LITMUS_DIR+'**/*.litmus', recursive=True)

with open(OUTPUT,'w') as writer:

    writer.write("# Test Results \n")
    writer.write("\n")
    writer.write("| Name       | JAM19        | JAM21     |\n")
    writer.write("|------------|------------|-----------|\n")

    for test in all_litmus_tests:
        testname = test.split('/')[len(test.split('/'))-1][:-7]
        print("Running: " + testname + " with JAM19")
        obs1    = get_result(JAM19, test)
        print("Running: " + testname + " with JAM21")
        obs2    = get_result(JAM21, test)
        writer.write("| "+testname+" | "+obs1+" | "+obs2+" |\n")
        print("| "+testname+" | "+obs1+" | "+obs2+" |")
