# Function Chain Laundering
Built for LLVM 19.1 - Windows x64 <br> <br>

This is a component of Nessa's homomorphism engine.<br> 
This is arguably one of the most important mechanisms to Nessa's homomorphism. We essentially take any function we can in the binary, clone it, then walk up the call chain, cloning everything up the chain. <br>
Once we fully map out the functions parenting, we insert loads of encryption keys from the top down, up to 8 functions of full on mutation, since every site is a single xref clone, you need to defeat every site, and recover its entire callgraph.<br>
Remember, every single call is indirected and encrypted, you can't walk backwards, only downwards from the entrypoint. <br>
Each key is passed down through parameters, as every function is unique, every call chain knows what it has to pass down and each function mutates it as it goes down. <br> 

<img width="605" height="289" alt="image" src="https://github.com/user-attachments/assets/5f908d10-7fb2-4c24-97fa-723cc89685d0" /> <br>
<img width="1363" height="801" alt="image" src="https://github.com/user-attachments/assets/bb335c1d-4953-4fdb-975e-14d5769fedba" /> <br>
<img width="854" height="199" alt="image" src="https://github.com/user-attachments/assets/e6bd9a40-e920-423c-bc10-8f6c86e825e4" />  <br>
<img width="687" height="414" alt="image" src="https://github.com/user-attachments/assets/14d679cf-de82-40c0-89a3-2435853cf120" /> <br>
<img width="720" height="222" alt="image" src="https://github.com/user-attachments/assets/6b36f373-055a-4fd5-b7b9-38df8d73eb5d" /> <br>

## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll
