#!/usr/bin/env python3
# report loc and number of pipeline stages for built programs.
import sys, subprocess, json, glob, os

usage = "./report_stats.py --single <build directory> | --multi <directory with many build directories>"

def main():
    if (len(sys.argv) != 3):
        print (usage)
        return
    if (sys.argv[1] == "--single"):
        measure_build(sys.argv[2])
    elif (sys.argv[1] == "--multi"):
        measure_builds(sys.argv[2])
    return

def measure_builds(builds_dir):
    builds = glob.glob("%s/*"%builds_dir)
    for build in builds:
        measure_build(build)
        print ("----------")

def measure_build(build_dir):
    """measure a lucid build directory"""
    lucid_src = glob.glob(build_dir + "/src/*.dpt")[0]
    print ("lucid program:%s"%lucid_src)
    resources = get_resources(log_dir_of_lucid_build(build_dir))
    resources["lucid loc"] = get_cloc(lucid_src)
    resources["p4 loc"] = str(int(get_cloc(build_dir+"/lucid.p4")) - int(get_cloc(build_dir+"/src/ip_harness.p4")))
    for (k, v) in resources.items():
        print ("%s: %s"%(k, v))
    return 

def get_cloc(src_fn): 
    cloc_cmd = """ cat {0} | grep -v "^ *$" | grep -v "^ *//" | grep -v "^ */\*.*\*/" | wc -l""".format(src_fn)
    res = subprocess.run(cloc_cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if ((int(res.stdout)) == 0):
        return "[p4 code not found]"
    else:
        return str(int(res.stdout))

def get_resources(log_dir):
    """
        get tables, sram, tcam, stages, salus, 
        phv bits, and vliw instruction counts
        from tofino compiler logs
    """
    sram_size = 16 # in KB
    tcam_size = 1.28 # in KB
    metrics = json.load(open(log_dir + "metrics.json", "r"))
    resources = json.load(open(log_dir + "resources.json", "r"))
    ret_dict = {}
    # logical tables
    ret_dict["Tables"] = int(metrics["mau"]["logical_tables"])  
    # SRAM (KB)
    ret_dict["SRAM (KB)"] = int(metrics["mau"]["srams"])*sram_size
    # TCAM (KB)
    ret_dict["TCAM (KB)"] = int(metrics["mau"]["tcams"])*tcam_size
    # stages
    ret_dict["Stages"] = len(resources["resources"]["mau"]["mau_stages"])
    # meter ALUs (sALUs)
    meter_ct = 0
    for stage in resources["resources"]["mau"]["mau_stages"]:
        meter_ct += len(stage["meter_alus"]["meters"])
    ret_dict["sALUs"] = meter_ct
    vliw_ct = 0
    for stage in resources["resources"]["mau"]["mau_stages"]:
        vliw_ct += len(stage["vliw"]["instructions"])
    ret_dict["vliw insrs"] = vliw_ct
    # metadata (bits)
    phv_util = 0
    for phv_type in metrics["phv"]["normal"]:
        phv_util += int(phv_type["bits_occupied"])
    for phv_type in metrics["phv"]["tagalong"]:
        phv_util += int(phv_type["bits_occupied"])
    ret_dict["PHV (b)"] = phv_util
    return ret_dict


def log_dir_of_lucid_build(build_dir): 
    return build_dir + "/lucid/pipe/logs/"

if __name__ == '__main__':
    main()