<div id="top"></div>

[![Contributors][contributors-shield]][contributors-url]

<!-- PROJECT LOGO -->
<br />
<h3 align="center">Attack Tree Modelling and Analysis Graphical Interface (ATMAGI)</h3>

  <p align="center">
    PyQT5 GUI Implementation for Attack Tree Analysis with various tools
  </p>
</div>

<!-- TABLE OF CONTENTS -->
<details>
  <summary>Table of Contents</summary>
  <ol>
    <li><a href="#about-the-project">About The Project</a></li>
    <li><a href="#installation">Install & Run</a></li>
    <li><a href="#usage">Usage</a></li>
  </ol>
</details>

<!-- ABOUT THE PROJECT -->
## About The Project

[![Product Name Screen Shot][product-screenshot]](https://github.com/weytho/AttackTree)

Implementation made by [Florentin Delcourt](https://github.com/delcourtfl) and [Thomas Weiser](https://github.com/weytho) for their master thesis.

<p align="right">(<a href="#top">back to top</a>)</p>


<!-- GETTING STARTED -->
## Install & Run

_Installer :_

1. Clone the repository
   ```sh
   git clone https://github.com/weytho/AttackTree.git
   ```
2. Run installer
   ```sh
   sh install.sh
   ```

_Package Launch :_

1. Run program
   ```sh
   atmagi_launcher
   ```

_Manual Launch :_

1. Compile C files from src/at_magi folder
   ```sh
   gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC C_utils/UtilsC.c -ljson-c
   ```
2. Run program from src/at_magi folder
   ```sh
   python ATMAGI.py
   ```

<p align="right">(<a href="#top">back to top</a>)</p>

<!-- USAGE EXAMPLES -->
## Usage

The implementation is launched from the 'ATMAGI.py' file in 'src/at_magi' folder.
'res' folder is used to store resources of the project (such as .json and .txt file).
Once launched the GUI display its main window with all its components.
Python requirements can be found in 'requirements.txt' file.

_For more detailled information, please refer to the [Documentation](https://github.com/weytho/AttackTree/blob/main/documentation.pdf)_

<p align="right">(<a href="#top">back to top</a>)</p>

<!-- MARKDOWN LINKS & IMAGES -->
<!-- https://www.markdownguide.org/basic-syntax/#reference-style-links -->
[contributors-shield]: https://img.shields.io/github/contributors/weytho/AttackTree.svg?style=for-the-badge
[contributors-url]: https://github.com/weytho/AttackTree/graphs/contributors
