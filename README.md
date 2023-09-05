## Exhaustive approach to 'The Liklihood of Non-Associativity of Floating Point Addition' 

### Introduction (TODO): 
This is a python script which simulates every possible Floating Point addition using [Titanic](https://github.com/billzorn/titanic) by Dr Bill Zorn and determines how often and when (a+b) + c ≠ a + (b + c) might occur. 


### Setup
This uses the [Titanic](https://github.com/billzorn/titanic) engine therefore you must be running a Linux machine. Recommended Operating System is Ubuntu 22.04.2 (It works for me, so it must work for you). <br> 
Follow the steps listed in [Titanic's](https://github.com/billzorn/titanic) repository to install the engine but you do not have to install the web tool. <br>
After getting Titanic to run, load the following files (fpsim.py and fpdebug.py) to /titanic/titanfp/tools/ <br>
Run the command `python3 -m titanfp.tools.fpsim`, the simulation should start running and you will be printed with all of the cases currently implemented

### What's left to do:
* Complete implementing Case 4 and Case 3 
* Implement multi-threading as it will decrease the time to run quite **significantly**
* Some other stuff as well