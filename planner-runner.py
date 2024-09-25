import os
import subprocess
import matplotlib.pyplot as plt
from matplotlib.backends.backend_pdf import PdfPages
import time

commands = [
    {
        "directory": ".",
        "label": "SAT",
        "domain": "gripper",
        "problem" : "p01",
        "command": [
            "java", "-cp", "classes;lib/pddl4j-4.0.0.jar;lib/sat4j-core-2.0rc1.jar",
            "fr.uga.pddl4j.examples.sat.SAT",
            "../src/test/resources/benchmarks/pddl/ipc1998/gripper/adl/domain.pddl",
            "../src/test/resources/benchmarks/pddl/ipc1998/gripper/adl/p01.pddl",
        ]
    },
        {
        "directory": ".",
        "label": "HSP",
        "problem" : "p01",
        "domain": "gripper",
        "command": [
            "java", "-cp", "classes;lib/pddl4j-4.0.0.jar",
            "fr.uga.pddl4j.examples.asp.ASP",
            "../src/test/resources/benchmarks/pddl/ipc1998/gripper/adl/domain.pddl",
            "../src/test/resources/benchmarks/pddl/ipc1998/gripper/adl/p01.pddl",
        ]
    },

    {
        "directory": ".",
        "label": "SAT",
        "domain": "blocks",
        "problem" : "p01",
        "command": [
            "java", "-cp", "classes;lib/pddl4j-4.0.0.jar",
            "fr.uga.pddl4j.examples.sat.SAT",
            "../src/test/resources/benchmarks/pddl/ipc2000/blocks/strips-typed/domain.pddl",
            "../src/test/resources/benchmarks/pddl/ipc2000/blocks/strips-typed/p001.pddl",
        ]
    },

        {
        "directory": ".",
        "label": "HSP",
        "domain": "blocks",
        "problem" : "p01",
        "command": [
            "java", "-cp", "classes;lib/pddl4j-4.0.0.jar",
            "fr.uga.pddl4j.examples.asp.ASP",
            "../src/test/resources/benchmarks/pddl/ipc2000/blocks/strips-typed/domain.pddl",
            "../src/test/resources/benchmarks/pddl/ipc2000/blocks/strips-typed/p001.pddl",
        ]
    },
     {
        "directory": ".",
        "label": "SAT",
        "domain": "blocks",
        "problem" : "p011",
        "command": [
            "java", "-cp", "classes;lib/pddl4j-4.0.0.jar",
            "fr.uga.pddl4j.examples.sat.SAT",
            "../src/test/resources/benchmarks/pddl/ipc2000/blocks/strips-typed/domain.pddl",
            "../src/test/resources/benchmarks/pddl/ipc2000/blocks/strips-typed/p010.pddl",
        ]
    },

        {
        "directory": ".",
        "label": "HSP",
        "domain": "blocks",
        "problem" : "p011",
        "command": [
            "java", "-cp", "classes;lib/pddl4j-4.0.0.jar",
            "fr.uga.pddl4j.examples.asp.ASP",
            "../src/test/resources/benchmarks/pddl/ipc2000/blocks/strips-typed/domain.pddl",
            "../src/test/resources/benchmarks/pddl/ipc2000/blocks/strips-typed/p010.pddl",
        ]
    },
    {
        "directory": ".",
        "label": "SAT",
        "domain": "depots",
        "problem" : "p01",
        "command": [
            "java", "-cp", "classes;lib/pddl4j-4.0.0.jar",
            "fr.uga.pddl4j.examples.sat.SAT",
            "../src/test/resources/benchmarks/pddl/ipc2002/depots/strips-automatic/domain.pddl",
            "../src/test/resources/benchmarks/pddl/ipc2002/depots/strips-automatic/p01.pddl",
        ]
    },

        {
        "directory": ".",
        "label": "HSP",
        "domain": "depots",
        "problem" : "p01",
        "command": [
            "java", "-cp", "classes;lib/pddl4j-4.0.0.jar",
            "fr.uga.pddl4j.examples.asp.ASP",
            "../src/test/resources/benchmarks/pddl/ipc2002/depots/strips-automatic/domain.pddl",
            "../src/test/resources/benchmarks/pddl/ipc2002/depots/strips-automatic/p01.pddl",
        ]
    },
  
]


# Storage for results
results = []
# Run each command and collect the metrics
for cmd in commands:
    os.chdir(cmd["directory"])
    print(cmd['domain'])
    start_time = time.time()
    result = subprocess.run(cmd["command"], capture_output=True, text=True)
    end_time = time.time()

    # Calculate the execution time in seconds
    execution_time = end_time - start_time
    # Extract time and makespan from the output
    output = result.stdout

    plan_start_idx = output.find("found plan as follows:") + len("found plan as follows:")
    plan_end_idx = output.find("time spent:")
    plan = output[plan_start_idx:plan_end_idx].strip().splitlines()
    makespan = len(plan)

    makespan = len(plan)




    results.append({
        "planner": cmd["label"],
        "domain": cmd['domain'], 
        "problem":cmd['problem'],    
        "time": execution_time,
        "makespan": makespan
    })


os.chdir("..")
# print(results)

# Separate the results by domain and planner
domain_results = {}
for result in results:
    key = f"{result['domain']}_{result['problem']}"
    if key not in domain_results:
        domain_results[key] = {"SAT": {}, "HSP": {}}
    domain_results[key][result["planner"]] = result


pdf_filename = "C:/Users/Bourahela/pddl4j/ASP/planner_comparisons.pdf"
with PdfPages(pdf_filename) as pdf:
    for key, data in domain_results.items():
        plt.figure(figsize=(10, 5))

        # Time comparison
        plt.subplot(1, 2, 1)
        plt.bar(["SAT", "HSP"], [data["SAT"]["time"], data["HSP"]["time"]], color=['red', 'black'])
        plt.title(f"{key} - Time Comparison")
        plt.ylabel("Time (s)")



        # Makespan comparison
        plt.subplot(1, 2, 2)
        plt.bar(["SAT", "HSP"], [data["SAT"]["makespan"], data["HSP"]["makespan"]], color=['red', 'black'])
        plt.title(f"{key} - Makespan Comparison")
        plt.ylabel("Makespan")

        # Save the figure in the PDF
        pdf.savefig()
        plt.suptitle(f"Comparison for {key}")
        plt.show()
        
        plt.close()

print(f"All plots have been saved to {pdf_filename}")