# gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testlib.c
from PyQt5.QtCore import QObject, QThread, pyqtSignal
import ctypes
import time

from PyQt5.QtWidgets import (
    QApplication,
    QLabel,
    QMainWindow,
    QPushButton,
    QVBoxLayout,
    QWidget,
)


so_file = "/home/flo/Desktop/Github/AttackTree/testlib.so"

my_function = ctypes.CDLL(so_file)

print(type(my_function))

my_function.main(10)

my_function.strGet.restype = ctypes.c_char_p
answer = my_function.strGet()
print(answer)

# Worker class
class Worker(QObject):
    finished = pyqtSignal()
    progress = pyqtSignal(int)

    def run(self):
        """Long-running task."""
        for i in range(5):
            time.sleep(1)
            self.progress.emit(i + 1)
            print(self.progress)
        self.finished.emit()

class Window(QMainWindow):

    def __init__(self, parent=None):

        super().__init__(parent)

        self.runLongTask()

    def runLongTask(self):
        # Step 2: Create a QThread object
        self.thread = QThread()
        # Step 3: Create a worker object
        self.worker = Worker()
        # Step 4: Move worker to the thread
        self.worker.moveToThread(self.thread)
        # Step 5: Connect signals and slots
        self.thread.started.connect(self.worker.run)
        self.worker.finished.connect(self.thread.quit)
        self.worker.finished.connect(self.worker.deleteLater)
        self.thread.finished.connect(self.thread.deleteLater)
        self.worker.progress.connect(self.reportProgress)
        # Step 6: Start the thread
        self.thread.start()

        # Final resets
        self.longRunningBtn.setEnabled(False)
        self.thread.finished.connect(
            lambda: self.longRunningBtn.setEnabled(True)
        )
        self.thread.finished.connect(
            lambda: self.stepLabel.setText("Long-Running Step: 0")
        )

Window()